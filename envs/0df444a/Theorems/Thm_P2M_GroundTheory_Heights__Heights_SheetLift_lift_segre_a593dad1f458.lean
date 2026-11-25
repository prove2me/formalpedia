-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetLift_lift_segre_a593dad1f458
-- name    : P2M_GroundTheory_Heights__Heights_SheetLift_lift_segre_a593dad1f458
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:32.501573+00:00
-- url     : https://prove2.me/theorems/9741470e-8098-4716-8205-3e34695b69a4
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Lift lift segre a593dad1f458: P2 M Ground Theory Heights  Heights Sheet Lift lift segre a593dad1f458
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Lift lift segre a593dad1f458 construction uses the P2 M Ground Theory Heights  Heights Sheet Lift lift segre a593dad1f458 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSheetLift.lean#L41-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSheetLift.lean#L41-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSheetLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSheetLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_bsmul_of_isMultiHomog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_prod_update_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet bsmul eval_bsmul_of_isMultiHomog
  prod_update_eq)
open GroundTheory.Heights₂.Heights.SheetLift
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_SheetLift_lift_segre_a593dad1f458 [DecidableEq K] (i0 : (k : K) → ι k) (k0 : K) {z : (Σ k, ι k) → ℂ}
    (hz : segre z i0 ≠ 0) :
    lift i0 k0 (segre z) = bsmul (fun k => (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetLift».«lift_segre» := P2M_GroundTheory_Heights__Heights_SheetLift_lift_segre_a593dad1f458
