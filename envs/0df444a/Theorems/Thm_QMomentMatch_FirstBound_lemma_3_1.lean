-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_lemma_3_1
-- name    : QMomentMatch.FirstBound.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:00:39.789945+00:00
-- url     : https://prove2.me/theorems/864ccea4-a3d0-459f-a3ab-9bab4a807c84
-- title:
--   Lemma 3.1 — symmetrization: $\Pr_{f\sim\mathcal D_{\mathbf c}}[\mathcal A^f=1]$ is a symmetric polynomial of degree $\le 2T$ in power sums of weighted degree $\le 2T$
-- statement:
--   Let $N\ge1$ and let $\mathcal A$ be a quantum algorithm making $T$ standard queries to $f:[N]\to[N]$, and put $d=2T$. Then there is a symmetric polynomial $P\in\mathbb R[x_1,\dots,x_N]$ of total degree at most $d$ such that for every feasible frequency vector $\mathbf c$ (that is, $\mathbf c\in\mathbb Z_{\ge0}^N$ with $\sum_j c_j=N$)
--   $$P(\mathbf c)=\Pr_{f\sim\mathcal D_{\mathbf c}}[\mathcal A^f=1]\in[0,1].$$
--   Moreover, if $d\ge1$, one can write $P(x)=F(p_1(x),\dots,p_d(x))$, where $p_j(x)=\sum_{i=1}^N x_i^j$ is the $j$-th power sum, $F\in\mathbb R[y_1,\dots,y_d]$, and every monomial $y_1^{\alpha_1}\cdots y_d^{\alpha_d}$ of $F$ satisfies
--   $$\sum_{j=1}^d j\,\alpha_j\le d .$$
--
--   This is the polynomial method adapted to inputs averaged over domain and range permutations: the weighted-degree condition is what makes the acceptance probability a univariate polynomial of degree $\le 2T$ in a single multiplicity (Lemma 3.9).
--
--   **Formalization Note** $P$ is an `MvPolynomial (Fin N) ℝ` evaluated at $(c_1,\dots,c_N)$; $F$ is an `MvPolynomial (Fin (2T)) ℝ` whose variable $j$ stands for $y_{j+1}$ and is substituted by `MvPolynomial.psum (Fin N) ℝ (j+1)`; "monomial of $F$" means a monomial in `F.support`.
--
--   Differences from the source:
--   - encoding: "making at most $T$ queries" → `QueryAlg … T` (exactly $T$ oracle calls); reason: an algorithm with $T'\le T$ queries gets the statement with $2T'\le 2T$, and renaming $F$'s variables into $y_1,\dots,y_{2T}$ keeps the weighted degree $\le 2T$.
--   - encoding: $f:[N]\to[N]$ and its oracle → `f : Fin N → ZMod N` with `xorOracle f`; reason: 0-based domain and labels $j\mapsto j\bmod N$; the oracle is the same unitary.
--   - encoding: variables $y_1,\dots,y_d$ → `Fin (2T)` with $y_{j+1}$ as index $j$; reason: index convention.
--   - encoding: final measurement → computational-basis measurement followed by a Boolean map; reason: a general two-outcome measurement folds into $U_T$.
--   - encoding: frequency vector c in D_c → vecMultiset c in dcMass; reason: D_c depends only on the multiset of fibre sizes; all feasible vectors are still quantified over.
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Lemma 3.1, p. 15

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QMomentMatch_FirstBound_InducedDist

namespace QMomentMatch.FirstBound

open QAlgorithms

/-- Lemma 3.1 (Symmetrization), p. 15. For a `T`-query algorithm, `d = 2T`. -/
theorem lemma_3_1 (N : ℕ) [NeZero N] (W : Type*) [Fintype W] [DecidableEq W] (T : ℕ)
    (alg : QueryAlg (Fin N) (ZMod N) W T) (out : (Fin N × ZMod N) × W → Bool) :
    ∃ P : MvPolynomial (Fin N) ℝ, P.IsSymmetric ∧ P.totalDegree ≤ 2 * T ∧
      (∀ c : Fin N → ℕ, IsFeasible c →
        MvPolynomial.eval (fun i => (c i : ℝ)) P = probAccept (dcMass (vecMultiset c)) alg out ∧
          probAccept (dcMass (vecMultiset c)) alg out ∈ Set.Icc (0 : ℝ) 1) ∧
      (1 ≤ 2 * T → ∃ F : MvPolynomial (Fin (2 * T)) ℝ,
        P = MvPolynomial.aeval (fun j : Fin (2 * T) => MvPolynomial.psum (Fin N) ℝ ((j : ℕ) + 1)) F ∧
          ∀ α ∈ F.support, ∑ j : Fin (2 * T), ((j : ℕ) + 1) * α j ≤ 2 * T) := by sorry

end QMomentMatch.FirstBound
