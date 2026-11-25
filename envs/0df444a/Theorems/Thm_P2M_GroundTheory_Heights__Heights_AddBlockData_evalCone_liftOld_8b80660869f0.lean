-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_evalCone_liftOld_8b80660869f0
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_evalCone_liftOld_8b80660869f0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:39.944734+00:00
-- url     : https://prove2.me/theorems/a0e2239e-5782-4846-ac39-e2c65c99003d
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data eval Cone lift Old 8b80660869f0: P2 M Ground Theory Heights  Heights Add Block Data eval Cone lift Old 8b80660869f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data eval Cone lift Old 8b80660869f0 construction uses the P2 M Ground Theory Heights  Heights Add Block Data eval Cone lift Old 8b80660869f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L47-L51

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_evalCone_liftOld_8b80660869f0 {F : Type*} [CommRing F] (w : Cone D.extSizes F) (f : MvPolynomial (Coord n) ℤ) :
    evalCone w (D.liftOld f) = evalCone (D.basePart₂ w) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«evalCone_liftOld» := P2M_GroundTheory_Heights__Heights_AddBlockData_evalCone_liftOld_8b80660869f0
