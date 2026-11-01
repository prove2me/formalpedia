-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_sqrtRescaling_range
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.sqrtRescaling_range
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:58:54.679171+00:00
-- url     : https://prove2.me/theorems/9a6a5381-6bc9-4071-ab3f-dfa1bafe2396
-- title:
--   Range of the square-root rescaling
-- statement:
--   Let $\gamma,s\in[0,1]$ and assume $1-\gamma s>0$, the domain of the displayed real quotient. Then
--
--   $$0\le\sqrt{\frac{1-\gamma}{1-\gamma s}}\le1.$$
--
--   This is the regular transverse rescaling factor of the positive-translation decomposition. No value is assigned at the singular pair $(1,1)$.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 12, Corollary 21

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF p.12, Corollary 21; the same regular domain correction. -/
theorem sqrtRescaling_range (gamma s30 : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (hs0 : 0 ≤ s30) (hs1 : s30 ≤ 1) (hden : 0 < 1-gamma*s30) :
    Real.sqrt (rescaling gamma s30) ∈ Set.Icc (0 : ℝ) 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
