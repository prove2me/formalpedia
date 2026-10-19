-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_bellDifferentOptimizers
-- name    : QAlgorithms.Papers.Independent.Information100.P21.bellDifferentOptimizers
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:04:48.824233+00:00
-- url     : https://prove2.me/theorems/d78c11ff-d1b8-4569-ac31-3427b432d38b
-- title:
--   III.B — separable and entangled optimal noises for a Bell state
-- statement:
--   For $\rho=|\Phi^+\rangle\langle\Phi^+|$, both robustnesses equal one. Two distinct normalized generalized-optimal noises are
--   $$Y_{\rm sep}=(|01\rangle\langle01|+|10\rangle\langle10|)/2,\qquad Y_{\rm ent}=|\Phi^-\rangle\langle\Phi^-|.$$
--   The first is separable and the second entangled, where $\Phi^\pm=(|00\rangle\pm|11\rangle)/\sqrt2$. Thus neither uniqueness nor separability of every generalized optimizer follows from equality of values.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 11, III.B — separable and entangled optimal noises for a Bell state

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 11, separable and entangled optimal noises for a Bell state. -/
theorem bellDifferentOptimizers  :
  let vplus : Vec QQ := ((Real.sqrt 2)⁻¹:ℂ) • (QAlgorithms.ket (0,0)+QAlgorithms.ket (1,1))
  let vminus : Vec QQ := ((Real.sqrt 2)⁻¹:ℂ) • (QAlgorithms.ket (0,0)-QAlgorithms.ket (1,1))
  let rho := proj vplus
  let Ysep := compressed true (1/2) (1/2)
  let Yent := proj vminus
  rs rho=1 ∧ rg rho=1 ∧ optG rho Ysep ∧ optG rho Yent ∧
  QAlgorithms.IsDensityMatrix Ysep ∧ QAlgorithms.IsDensityMatrix Yent ∧
  sep Ysep ∧ ¬sep Yent ∧ Ysep≠Yent := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
