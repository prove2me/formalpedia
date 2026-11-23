-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Phi_map
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Phi_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:03.664082+00:00
-- url     : https://prove2.me/theorems/98fe5b5c-ed21-4871-802e-67b0e4d32bf4
-- title:
--   Units Filt: Phi map
-- statement:
--   The Units Filt construction uses the Phi map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandC.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandC.lean#L22-L31

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Phi_map (σ : L ≃ₐ[K] L) (x : L) (τ : L ≃ₐ[K] L) : Phi K L (σ x) τ = Phi K L x (σ⁻¹ * τ) := by sorry
