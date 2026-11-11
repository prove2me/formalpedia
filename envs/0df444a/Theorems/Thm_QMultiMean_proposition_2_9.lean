-- Prove2me | Theorems.Thm_QMultiMean_proposition_2_9
-- name    : QMultiMean.proposition_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:46.666216+00:00
-- url     : https://prove2.me/theorems/155c411b-b0fb-4ec3-93cf-349c14df41ba
-- title:
--   Proposition 2.9 — quantum quantile estimator [Ham21] with $O(\log(1/\delta)/\sqrt p)$ queries (corrected: $O(\max\{1,\log(1/\delta)\}/\sqrt p)$)
-- statement:
--   There are universal constants $c\in(0,1)$ and $C$ such that the following holds. Let $p,\delta\in(0,1)$. There is a quantum estimator, chosen from $p,\delta$, $\Omega$ and $E$ only, using at most
--   $$C\,\frac{\max\{1,\log(1/\delta)\}}{\sqrt p}$$
--   quantum experiments and binary oracle queries, such that for every finite real-valued random variable $X:\Omega\to E$ and every quantum experiment and binary oracle of $X$ it returns $\tilde Q$ with
--   $$Q(p)\le\tilde Q\le Q(cp)$$
--   with probability at least $1-\delta$, where $Q$ is the quantile function of $X$.
--
--   Algorithm 2 uses it to find the levels $a_j\approx Q(2^{-j})$ of $\|Y\|_2$ at which it slices $Y$.
--
--   Differences from the source:
--   - reading: an informal quantum estimator / algorithm using quantum experiments and binary oracle queries → an oracle circuit (unitary gates, calls to U_P, U_P⁻¹, B_X, B_X⁻¹ on copies of H_Ω⊗H_E, final computational-basis measurement, classical output map) chosen from the parameters, Ω and E before P, X and the oracles, and successful for every pair of unitaries meeting Definitions 2.5–2.6; reason: the paper defines no model of computation; this is the standard query model its proofs use, and the oracles are specified only on |0⟩ and |ω⟩|0⃗⟩
--   - correction: O(log(1/δ)/√p) quantum experiments and binary oracle queries → at most C·max(1, log(1/δ))/√p calls, with c chosen first and then a universal C; reason: the literal bound tends to 0 (as δ → 1) and then allows 0 queries; counterexample: on Ω = {0} take E containing 0 and K > 1/(1−δ) distinct constants c₁, …, c_K and X ≡ c_i; then Q(p) = Q(cp) = c_i, a 0-query estimator has one output law for all i, so it cannot output each c_i with probability ≥ 1 − δ
--   - generalization: E ⊂ ℝ^d the finite support of X, with 0⃗ ∈ E assumed (Definitions 2.2, 2.6) → E any finite set containing 0 and every value X(ω); reason: the support together with 0 is one admissible E, so the statement specializes to the source's
--   - encoding: a finite sample set Ω with 0 ∈ Ω → Ω = Fin (N+1) with distinguished point 0; reason: every finite pointed set is in bijection with some Fin (N+1); the estimator may depend on Ω anyway
--   - reading: log (base not stated) → natural logarithm Real.log; reason: the natural log gives the weaker hypothesis n ≥ log(d/δ) and the smaller error bound, so it is the stronger reading; a base change is absorbed by the query constant
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.8, Proposition 2.9

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_quantile
import Definitions.Def_QMultiMean_IsBinaryOracle
import Definitions.Def_QMultiMean_OracleCircuit

set_option autoImplicit false

namespace QMultiMean

/-- Proposition 2.9 (Quantile estimator, [Ham21]) of Cornelissen, Hamoudi, Jerbi,
arXiv:2111.09787v2, p.8: let `X` be a univariate random variable. Given reals `p, δ ∈ (0, 1)`, the
quantile estimation algorithm `Quantile(X, p, δ)` returns `Q̃` with `Q(p) ≤ Q̃ ≤ Q(cp)` with
probability at least `1 − δ`, for some universal constant `c ∈ (0, 1)`, using `O(log(1/δ)/√p)`
quantum experiments and binary oracle queries to `X`.

**Formalization Note.** `c` is chosen first, then the constant `C` of `O(·)`. The algorithm is an
estimator built from `p, δ, N, E` before the instance and the oracles, successful for every pair of
oracles meeting Definitions 2.5–2.6. `O(log(1/δ)/√p)` is `C·max(1, log(1/δ))/√p`; the `max(1, ·)`
corrects the literal bound, which allows `0` queries as `δ → 1`. `Q` is the quantile of
Definition 2.3 for the law of `X` under `P`. Natural log. -/
theorem proposition_2_9 :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ C : ℝ, ∀ (p δ : ℝ), 0 < p → p < 1 → 0 < δ → δ < 1 →
      ∀ (N : ℕ) (E : Finset ℝ) (h0 : (0 : ℝ) ∈ E),
      ∃ M : Estimator N E ℝ,
        (M.T : ℝ) ≤ C * max 1 (Real.log (1 / δ)) / Real.sqrt p ∧
        ∀ (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → ℝ), IsPMF P → (∀ ω, X ω ∈ E) →
          ∀ (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
            (B : Matrix (Fin (N + 1) × E) (Fin (N + 1) × E) ℂ),
            IsQuantumExperiment P U → IsBinaryOracle E h0 X B →
            1 - δ ≤ M.successProb h0 U B
              {q | quantile P X p ≤ q ∧ q ≤ quantile P X (c * p)} := by sorry

end QMultiMean
