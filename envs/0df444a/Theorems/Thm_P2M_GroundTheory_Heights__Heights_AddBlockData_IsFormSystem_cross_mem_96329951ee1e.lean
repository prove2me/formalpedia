-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_IsFormSystem_cross_mem_96329951ee1e
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_IsFormSystem_cross_mem_96329951ee1e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:49.990745+00:00
-- url     : https://prove2.me/theorems/5d34df63-295c-468d-be3e-dd10685f923e
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data Is Form System cross mem 96329951ee1e: P2 M Ground Theory Heights  Heights Add Block Data Is Form System cross mem 96329951ee1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data Is Form System cross mem 96329951ee1e construction uses the P2 M Ground Theory Heights  Heights Add Block Data Is Form System cross mem 96329951ee1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L70-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L70-L81

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_IsFormSystem_cross_mem_96329951ee1e {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) (c c' : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)) :
    chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«IsFormSystem».«cross_mem» := P2M_GroundTheory_Heights__Heights_AddBlockData_IsFormSystem_cross_mem_96329951ee1e
