-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_liftOld_of_isWeightedHomogeneous_026a3ff1a179
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_liftOld_of_isWeightedHomogeneous_026a3ff1a179
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:06.598847+00:00
-- url     : https://prove2.me/theorems/33c74cf2-5381-457f-9100-e3c396b674fe
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data ext Map lift Old of is Weighted Homogeneous 026a3ff1a179: P2 M Ground Theory Heights  Heights Add Block Data ext Map lift Old of is Weighted Homogene
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data ext Map lift Old of is Weighted Homogeneous 026a3ff1a179 construction uses the P2 M Ground Theory Heights  Heights Add Block Data ext Map lift Old of is Weighted Homogeneous 026a3ff1a179 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L33-L45

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_liftOld_of_isWeightedHomogeneous_026a3ff1a179 {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    D.extMap (D.liftOld f) = C (P.mkF f) * ∏ k, X (some k) ^ δ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«extMap_liftOld_of_isWeightedHomogeneous» := P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_liftOld_of_isWeightedHomogeneous_026a3ff1a179
