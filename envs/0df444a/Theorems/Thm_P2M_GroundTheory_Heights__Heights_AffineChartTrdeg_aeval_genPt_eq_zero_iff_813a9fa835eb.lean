-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_eq_zero_iff_813a9fa835eb
-- name    : P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_eq_zero_iff_813a9fa835eb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:02:42.182434+00:00
-- url     : https://prove2.me/theorems/fde91599-212b-4bf3-a571-d2d9c279573a
-- title:
--   P2 M Ground Theory Heights  Heights Affine Chart Trdeg aeval gen Pt eq zero iff 813a9fa835eb: P2 M Ground Theory Heights  Heights Affine Chart Trdeg aeval gen Pt eq zero iff 813a9fa835eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Affine Chart Trdeg aeval gen Pt eq zero iff 813a9fa835eb construction uses the P2 M Ground Theory Heights  Heights Affine Chart Trdeg aeval gen Pt eq zero iff 813a9fa835eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PAffineChartTrdeg.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PAffineChartTrdeg.lean#L27-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PAffineChartTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AffineChartTrdeg
variable {F : Type} [Field F] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
omit [P.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_eq_zero_iff_813a9fa835eb (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = 0 ↔ f ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AffineChartTrdeg».«aeval_genPt_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_eq_zero_iff_813a9fa835eb
