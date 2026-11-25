-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_norm_Phi_le
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.norm_Phi_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:51:39.191057+00:00
-- url     : https://prove2.me/theorems/0708f660-b7bf-56d2-98b4-cf9aa53340d8
-- title:
--   Units Filt: norm Phi le
-- statement:
--   The Units Filt construction uses the norm Phi le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandC.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandC.lean#L71-L72

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.norm_Phi_le (x : L) : ‖Phi K L x‖ ≤ ‖(Phi K L : L →L[K] ((L ≃ₐ[K] L) → K))‖ * ‖x‖ := by sorry
