-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_transcendental_bb27ef9817ff
-- name    : P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_transcendental_bb27ef9817ff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:17.824803+00:00
-- url     : https://prove2.me/theorems/c389065b-cddc-493b-8627-bd2179ce0e29
-- title:
--   P2 M Ground Theory Heights  Heights Affine Chart Trdeg transcendental bb27ef9817ff: P2 M Ground Theory Heights  Heights Affine Chart Trdeg transcendental bb27ef9817ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Affine Chart Trdeg transcendental bb27ef9817ff construction uses the P2 M Ground Theory Heights  Heights Affine Chart Trdeg transcendental bb27ef9817ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PAffineChartTrdeg.lean#L63-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PAffineChartTrdeg.lean#L63-L117

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

theorem P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_transcendental_bb27ef9817ff (hP : IsHomogIdeal P) (j : Fin n) (hj : X j ∉ P) :
    Transcendental (Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹))
      (genPt P j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AffineChartTrdeg».«transcendental» := P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_transcendental_bb27ef9817ff
