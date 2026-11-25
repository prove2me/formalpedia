-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_liftOld_mem_extIdeal_ea5e70b5cf5c
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_liftOld_mem_extIdeal_ea5e70b5cf5c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:46.984049+00:00
-- url     : https://prove2.me/theorems/5c0368c0-6251-40af-b2b2-c2036884a0fc
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data lift Old mem ext Ideal ea5e70b5cf5c: P2 M Ground Theory Heights  Heights Add Block Data lift Old mem ext Ideal ea5e70b5cf5c
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data lift Old mem ext Ideal ea5e70b5cf5c construction uses the P2 M Ground Theory Heights  Heights Add Block Data lift Old mem ext Ideal ea5e70b5cf5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L53-L61

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_liftOld_mem_extIdeal_ea5e70b5cf5c {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ P.ideal) :
    D.liftOld f ∈ D.extIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«liftOld_mem_extIdeal» := P2M_GroundTheory_Heights__Heights_AddBlockData_liftOld_mem_extIdeal_ea5e70b5cf5c
