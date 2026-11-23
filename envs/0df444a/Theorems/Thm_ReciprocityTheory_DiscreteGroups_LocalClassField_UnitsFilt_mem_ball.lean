-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_mem_ball
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.mem_ball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:35.006072+00:00
-- url     : https://prove2.me/theorems/464d34cd-1cfa-4fae-a091-ace1cc2c0830
-- title:
--   Units Filt: mem ball
-- statement:
--   The Units Filt construction uses the mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandC.lean#L102-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandC.lean#L102-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
open Finset
variable (K L : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.mem_ball {t : ℝ} {ht : 0 ≤ t} {x : L} : x ∈ ball K L t ht ↔ ‖Phi K L x‖ ≤ t := by sorry
