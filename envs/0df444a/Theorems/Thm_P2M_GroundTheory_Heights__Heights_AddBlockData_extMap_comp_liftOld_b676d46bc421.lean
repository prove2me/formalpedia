-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_comp_liftOld_b676d46bc421
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_comp_liftOld_b676d46bc421
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:17.659285+00:00
-- url     : https://prove2.me/theorems/9dd7edfe-a4e1-4efe-81ae-cdc57a57d415
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data ext Map comp lift Old b676d46bc421: P2 M Ground Theory Heights  Heights Add Block Data ext Map comp lift Old b676d46bc421
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data ext Map comp lift Old b676d46bc421 construction uses the P2 M Ground Theory Heights  Heights Add Block Data ext Map comp lift Old b676d46bc421 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L17-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExtMapLiftOldOfIsWeightedHomogeneous
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
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_comp_liftOld_b676d46bc421 :
    D.extMap.comp D.liftOld.toRingHom =
      eval₂Hom (Int.castRingHom _) fun v : Coord n ↦ C (P.mkF (X v)) * X (some v.1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«extMap_comp_liftOld» := P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_comp_liftOld_b676d46bc421
