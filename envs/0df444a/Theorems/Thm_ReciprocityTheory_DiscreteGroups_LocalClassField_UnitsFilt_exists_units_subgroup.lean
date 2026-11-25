-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_exists_units_subgroup
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.exists_units_subgroup
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:56.630222+00:00
-- url     : https://prove2.me/theorems/7060d545-120f-4f2d-a653-a129f3f9f0e1
-- title:
--   Units Filt: exists units subgroup
-- statement:
--   The Units Filt construction uses the exists units subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandD.lean#L85-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandD.lean#L85-L119

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandD
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
variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.exists_units_subgroup [IsUltrametricDist L] : ∃ S : Subgroup Lˣ,
    (∀ (σ : L ≃ₐ[K] L) (u v : Lˣ), u ∈ S → (v : L) = σ u → v ∈ S) ∧
    (∀ u ∈ S, ‖(u : L)‖ = 1) ∧ (∃ ε : ℝ, 0 < ε ∧ ∀ u : Lˣ, ‖(u : L) - 1‖ < ε → u ∈ S) ∧
    (∀ u ∈ S, (∀ σ : L ≃ₐ[K] L, σ (u : L) = u) → ∃ v ∈ S, ∏ σ : L ≃ₐ[K] L, σ (v : L) = u) ∧
    ∀ σ₀ : L ≃ₐ[K] L, (∀ σ, σ ∈ Subgroup.zpowers σ₀) → ∀ u ∈ S, ∏ σ : L ≃ₐ[K] L, σ (u : L) = 1 →
      ∃ v ∈ S, σ₀ (v : L) = u * v := by sorry
