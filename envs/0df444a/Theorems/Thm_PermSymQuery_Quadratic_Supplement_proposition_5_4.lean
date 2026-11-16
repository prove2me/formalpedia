-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_Supplement_proposition_5_4
-- name    : PermSymQuery.Quadratic.Supplement.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:40:39.513215+00:00
-- url     : https://prove2.me/theorems/47057b69-5b1b-4f88-93dd-11521c052829
-- title:
--   Proposition 5.4 — bias-preserving nonadaptive simulation for hypergraph properties
-- statement:
--   For every integer $k\ge2$ there is a positive natural constant $C_k$, depending only on $k$, with the following property. Let $N$ be any natural number and let $f$ be a $k$-uniform hypergraph property on $[N]$ with promise $D$. Let $T\ge1$ and $0<\beta\le1/2$. Suppose a quantum algorithm with any finite workspace, making $T'\le T$ queries to the ordered-tuple hypergraph oracle, satisfies
--   $$\Pr[\mathcal A(H)=f(H)]\ge\frac12+\beta\qquad(H\in D).$$
--   Then there is a nonadaptive randomized decision tree $R$ over hyperedge-membership queries such that every tree in its support makes at most $C_kT^{2k}$ queries on every input and
--   $$\Pr[R(H)=f(H)]\ge\frac12+\frac{3\beta}4\qquad(H\in D).$$
--   The constant does not depend on $N$, the promise, the property, $T$, $\beta$ or the quantum algorithm. No size condition on $N$ is imposed; the full-input case is included.
--
--   This is the single-run simulation whose majority of three runs gives Theorem 1.2.
--
--   Differences from the source:
--   - encoding: vertex set [N], ordered vertex tuples, one answer bit and signed outputs → Fin N, Fin k → Fin N, ZMod 2, and output probabilities of true and false; reason: these relabel the vertices and registers and preserve the signed expectation Pr[1] − Pr[0]
--   - encoding: arbitrary finite quantum workspaces and two-outcome measurements → published QueryAlg with an arbitrary finite workspace and a Boolean computational-basis output map; reason: input-independent final unitaries and ancillary registers realize every source measurement without additional queries (the base mission's convention)
--   - encoding: a partial k-uniform hypergraph property f : D ⊆ {0,1}^([N] choose k) → {0,1} → a Bool-valued function on all hypergraphs with HypPermInvariant D f, used only on D; reason: the values of f outside D are never read; every source instance, including the empty promise, is represented
--   - encoding: a randomized algorithm using O_k(T^{2k}) queries → for each k ≥ 2 one positive natural C, quantified before every other datum, and a PMF over decision trees with at most C * T^(2k) queries on every supported tree and input; reason: the O_k constant depends only on k, and a positive real constant can be rounded up to a natural one
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Proposition 5.4, PDF p. 24 (printed p. 22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Supplement_Hypergraph

namespace PermSymQuery.Quadratic.Supplement

/-- Proposition 5.4, PDF p.24 (printed p.22): for each `k ≥ 2` one constant `C_k`, independent
of `N`, the promise, the property, `T`, `β` and the quantum algorithm; nonadaptive simulation
with success probability `1/2 + 3β/4`. -/
theorem proposition_5_4 : ∀ k : ℕ, 2 ≤ k → ∃ C : ℕ, 0 < C ∧
    ∀ (N : ℕ) (D : Set (Hypergraph (Fin N) k)) (f : Hypergraph (Fin N) k → Bool),
      HypPermInvariant D f →
    ∀ (T : ℕ), 1 ≤ T → ∀ (β : ℝ), 0 < β → β ≤ 1 / 2 →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (T' : ℕ), T' ≤ T →
    ∀ (alg : QAlgorithms.QueryAlg (Fin k → Fin N) (ZMod 2) W T')
      (out : HStateIndex N k W → Bool),
      (∀ H ∈ D, (1 : ℝ) / 2 + β ≤ alg.outputProb (hypOracle H) out (f H)) →
      ∃ R : QAlgorithms.RandDecisionTree (KSet (Fin N) k) Bool Bool,
        HNonadaptive R ∧ QAlgorithms.RandMakesAtMost R (C * T ^ (2 * k)) ∧
        ∀ H ∈ D, (1 : ℝ) / 2 + 3 * β / 4 ≤ QAlgorithms.successProb R H (f H) := by sorry

end PermSymQuery.Quadratic.Supplement
