-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_179a6d344b31
-- name    : P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_179a6d344b31
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:03:38.491782+00:00
-- url     : https://prove2.me/theorems/a16116e5-aaa6-4e6f-b237-9095178b7953
-- title:
--   P2 M Ground Theory Heights  Heights Affine Chart Trdeg aeval gen Pt 179a6d344b31: P2 M Ground Theory Heights  Heights Affine Chart Trdeg aeval gen Pt 179a6d344b31
-- statement:
--   The P2 M Ground Theory Heights  Heights Affine Chart Trdeg aeval gen Pt 179a6d344b31 construction uses the P2 M Ground Theory Heights  Heights Affine Chart Trdeg aeval gen Pt 179a6d344b31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PAffineChartTrdeg.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PAffineChartTrdeg.lean#L16-L23

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

theorem P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_179a6d344b31 (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = algebraMap (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (Ideal.Quotient.mk P f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AffineChartTrdeg».«aeval_genPt» := P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_179a6d344b31
