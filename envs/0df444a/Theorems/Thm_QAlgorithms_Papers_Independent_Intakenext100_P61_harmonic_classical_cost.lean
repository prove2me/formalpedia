-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_harmonic_classical_cost
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.harmonic_classical_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:21:51.198984+00:00
-- url     : https://prove2.me/theorems/38137c95-f761-4f35-96af-2742b6fa7a18
-- title:
--   §IV, unnumbered: asymptotically tight classical preparation cost
-- statement:
--   Let $\varepsilon_n\ge0$ tend to zero, and let $|\mu_n\rangle=H_n^{-1/2}\sum_{i=1}^ni^{-1/2}|i,i\rangle$, where $H_n=\sum_{i=1}^n1/i$. For every slack $s>0$, there is $N\ge2$, uniform over EPR supplies and deterministic classical-only preparation protocols, such that for all $n\ge N$, unconditional squared fidelity at least $1-\varepsilon_n$ requires
--
--   $$C\ge(1-s)\log_2 n.$$
--
--   Equivalently, the universal asymptotic lower ratio is at least one. This interprets the printed $1-o(1)$ coefficient in the asymptotically faithful regime; Lo's cited upper bound is not restated as a new theorem.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 8, §IV, unnumbered: asymptotically tight classical preparation cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

/-- PDF p.8, unnumbered classical preparation bound: the printed (1-o(1))
coefficient is interpreted in the asymptotically faithful regime epsilon_n -> 0,
not at fixed nonzero error. Lo's upper bound is background, not a new assertion.
The displayed eventual bound is the universal liminf >= 1 formulation. -/
theorem harmonic_classical_cost (epsilon : ℕ → ℝ) (hzero : ∀ n, 0 ≤ epsilon n)
    (hfaithful : Filter.Tendsto epsilon Filter.atTop (nhds 0)) :
    ∀ slack : ℝ, 0 < slack → ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N, ∀ (k : ℕ) (cost : ℝ),
      ClassicalPrepares (eprPairs k) (harmonicState n) (epsilon n) cost →
      (1 - slack) * logTwo n ≤ cost := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
