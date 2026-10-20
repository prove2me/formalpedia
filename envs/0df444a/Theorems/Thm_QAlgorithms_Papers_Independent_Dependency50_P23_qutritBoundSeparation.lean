-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_qutritBoundSeparation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.qutritBoundSeparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:46:15.302982+00:00
-- url     : https://prove2.me/theorems/bed5ba19-2e25-433d-be15-4f9e83fe8afd
-- title:
--   Unnumbered remark: β is strictly smaller than ζ for the qutrit family
-- statement:
--   Let $0<\alpha\le\pi/4$, and let $\mathcal N_\alpha$ be the qutrit channel with Kraus operators $\sin\alpha|0\rangle\langle1|+|1\rangle\langle2|$ and $\cos\alpha|2\rangle\langle1|+|1\rangle\langle0|$. Then
--
--   $$C_\beta(\mathcal N_\alpha)<C_E(\mathcal N_\alpha),\qquad C_\beta(\mathcal N_\alpha)<C_\zeta(\mathcal N_\alpha).$$
--
--   The two SDP quantities are logarithms of the respective attained programs; $C_E$ is entanglement-assisted capacity in bits per use. This is a family-specific separation and asserts no universal ordering between beta and zeta.
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

/-- PDF p.19, unnumbered remark: beta strictly below EA and zeta on this family. -/
theorem qutritBoundSeparation (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha ≤ Real.pi/4) :
    cBeta (qutrit alpha) < eaCapacity (qutrit alpha) ∧
    cBeta (qutrit alpha) < cZeta (qutrit alpha) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
