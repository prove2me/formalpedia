-- Prove2me | Theorems.Thm_QuantumMC_MeanEst_theorem_5_l2_bound
-- name    : QuantumMC.MeanEst.theorem_5_l2_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:06.261999+00:00
-- url     : https://prove2.me/theorems/a372e09d-f9a4-4232-9e68-b55c267b6bc8
-- title:
--   §2.3, proof of Theorem 5 — centered norm bound
-- statement:
--   Let $X$ have variance at most $\sigma^2$ with $\sigma>0$. If the sampled value $m$ obeys $|m-\mathbb E[X/\sigma]|\le3$, then the centered output $B=X/\sigma-m$ satisfies
--
--   $$\|B\|_2\le4.$$
--
--   This is the bounded-norm condition used when Algorithm 2 is applied to the two parts of $B$.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §2.3, proof of Theorem 5, p. 12

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

namespace QuantumMC.MeanEst

open MeasureTheory ProbabilityTheory

/-- §2.3, proof of Theorem 5, p. 12: the centered output has L² norm at most four. -/
theorem theorem_5_l2_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hXm : Measurable X)
    (hX : MemLp X 2 P) (σ : ℝ) (hvar : variance X P ≤ σ ^ 2)
    (hσ : 0 < σ) (m : ℝ) (hm : |m - ∫ x, X x / σ ∂P| ≤ 3) :
    l2norm P (alg3B σ m X) ≤ 4 := by sorry
end QuantumMC.MeanEst
