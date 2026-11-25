-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_exists_isHomogeneous_5524448663c0
-- name    : P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_exists_isHomogeneous_5524448663c0
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:21.294851+00:00
-- url     : https://prove2.me/theorems/af6c77e2-722b-4d32-bd58-8fb93e7c3b06
-- title:
--   P2 M Ground Theory Heights  Heights Affine Chart Trdeg exists is Homogeneous 5524448663c0: P2 M Ground Theory Heights  Heights Affine Chart Trdeg exists is Homogeneous 5524448663c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Affine Chart Trdeg exists is Homogeneous 5524448663c0 construction uses the P2 M Ground Theory Heights  Heights Affine Chart Trdeg exists is Homogeneous 5524448663c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PAffineChartTrdeg.lean#L31-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PAffineChartTrdeg.lean#L31-L61

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

theorem P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_exists_isHomogeneous_5524448663c0 (j : Fin n) (hj : genPt P j ≠ 0)
    {a : FractionRing (MvPolynomial (Fin n) F ⧸ P)}
    (ha : a ∈ Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)) :
    ∃ D : ℕ, ∀ D' ≥ D, ∃ h : MvPolynomial (Fin n) F,
      h.IsHomogeneous D' ∧ aeval (genPt P) h = a * genPt P j ^ D' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AffineChartTrdeg».«exists_isHomogeneous» := P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_exists_isHomogeneous_5524448663c0
