-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_cauchy_schwarz_4_10
-- name    : PoissonDepTrials.MixSqrt.cauchy_schwarz_4_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:27.282397+00:00
-- url     : https://prove2.me/theorems/3be77213-1cbb-4946-b112-02c4780b6070
-- title:
--   (4.10), p. 540 — ΣΣ_{|i−j|≤m} p_ip_j ≤ (2m + 1) Σ_i p_i²
-- statement:
--   Let $p_1,\dots,p_n$ be real numbers and $m\ge0$ an integer. Then
--   $$\sum\sum_{|i-j|\le m}p_ip_j\le(2m+1)\sum_{i=1}^np_i^2,$$
--   the double sum running over pairs $i,j\in\{1,\dots,n\}$ with $|i-j|\le m$.
--
--   In the paper the $p_i$ are the success probabilities of the trials; the inequality converts the third error term of (2.6) into the $\sum p_i^2$ term of Theorem 4.1.
--
--   **Formalization Note** The statement is made for arbitrary real $p_i$, which is stronger than the paper's use (probabilities) and implies it.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 540, proof of Lemma 4.5, (4.10)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), proof of Lemma 4.5, p. 540, (4.10), stated for an arbitrary real sequence
`p_1, …, p_n`: `ΣΣ_{|i−j|≤m} p_ip_j ≤ (2m + 1) Σ_{i=1}^n p_i²`. -/
theorem cauchy_schwarz_4_10 (n m : ℕ) (p : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m, p i * p j
      ≤ (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, p i ^ 2 := by sorry

end PoissonDepTrials.MixSqrt
