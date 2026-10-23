-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_qutritClassification
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.qutritClassification
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:46:57.20014+00:00
-- url     : https://prove2.me/theorems/eb615ca8-9109-4015-9dfb-97b950d728e9
-- title:
--   Unnumbered remark: the qutrit family is neither EB nor Hadamard
-- statement:
--   For $0<\alpha\le\pi/4$, let $\mathcal N_\alpha$ have Kraus operators $\sin\alpha|0\rangle\langle1|+|1\rangle\langle2|$ and $\cos\alpha|2\rangle\langle1|+|1\rangle\langle0|$. Then
--
--   $$\mathcal N_\alpha\text{ is neither entanglement breaking nor Hadamard.}$$
--
--   Entanglement breaking means that every finite reference extension maps density inputs to separable positive outputs. Hadamard means that an isometric dilation has an entanglement-breaking complementary channel. The result distinguishes this strong-converse family from these two previously studied channel classes.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 19, Unnumbered remark

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF p.19, unnumbered remark: neither EB nor Hadamard; this does not claim
membership information about the undefined external classes of reference [17]. -/
theorem qutritClassification (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha ≤ Real.pi/4) :
    ¬ IsEB (qutrit alpha) ∧ ¬ IsHadamard (qutrit alpha) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
