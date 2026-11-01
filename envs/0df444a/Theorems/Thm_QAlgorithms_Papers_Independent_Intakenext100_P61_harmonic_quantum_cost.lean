-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_harmonic_quantum_cost
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.harmonic_quantum_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:21:07.678994+00:00
-- url     : https://prove2.me/theorems/af9542e8-8822-42df-a9d6-15cde87d7dd0
-- title:
--   §IV, unnumbered: logarithmic quantum preparation lower bound
-- statement:
--   Fix $0\le\varepsilon<1/4$ and put $\delta=(4\varepsilon)^{1/8}$. Let $|\mu_n\rangle=H_n^{-1/2}\sum_{i=1}^ni^{-1/2}|i,i\rangle$, where $H_n=\sum_{i=1}^n1/i$. There are $K>0$ and $N\ge4$, chosen before $n$, the finite EPR supply and the protocol, such that every deterministic quantum protocol preparing $\mu_n$ with squared fidelity at least $1-\varepsilon$ satisfies
--
--   $$C\ge(\tfrac12-\delta)\log_2 n-K\log_2\log_2 n\qquad(n\ge N).$$
--
--   The constants may depend on the fixed error. The leading coefficient is positive in the smaller regime $\delta<1/2$.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 8, §IV, unnumbered: logarithmic quantum preparation lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

/-- PDF p.8, unnumbered quantum preparation bound: for each fixed epsilon,
the O(log log n) constant and threshold are uniform over every EPR supply and
protocol. The leading coefficient is positive when delta<1/2. -/
theorem harmonic_quantum_cost (epsilon : ℝ) (hzero : 0 ≤ epsilon) (hsmall : epsilon < 1 / 4) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 4 ≤ N ∧ ∀ n ≥ N, ∀ (k : ℕ) (cost : ℝ),
      QuantumPrepares (eprPairs k) (harmonicState n) epsilon cost →
      (1 / 2 - smoothingError epsilon) * logTwo n - K * logTwo (logTwo n) ≤ cost := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
