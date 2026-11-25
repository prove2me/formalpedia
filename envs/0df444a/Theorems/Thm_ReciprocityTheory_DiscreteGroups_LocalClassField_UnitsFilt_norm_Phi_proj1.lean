-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_norm_Phi_proj1
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.norm_Phi_proj1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:51:57.967952+00:00
-- url     : https://prove2.me/theorems/8a517f41-9c37-44eb-b8ab-41f8afb9bb31
-- title:
--   Units Filt: norm Phi proj1
-- statement:
--   The Units Filt construction uses the norm Phi proj1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandC.lean#L46-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandC.lean#L46-L57

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.norm_Phi_proj1 (x : L) : ‖Phi K L (proj1 K L x)‖ ≤ ‖Phi K L x‖ := by sorry
