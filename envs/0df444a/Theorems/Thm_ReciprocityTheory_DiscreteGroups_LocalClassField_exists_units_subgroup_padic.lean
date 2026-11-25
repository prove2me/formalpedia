-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_units_subgroup_padic
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.exists_units_subgroup_padic
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:36.000025+00:00
-- url     : https://prove2.me/theorems/c5c0858e-bda9-523c-b4b9-b8dcba18df7c
-- title:
--   Local Class Field: exists units subgroup padic
-- statement:
--   The Local Class Field construction uses the exists units subgroup padic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandE.lean#L12-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandE.lean#L12-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.exists_units_subgroup_padic (hK : FiniteDimensional ℚ_[p] K) (E : IntermediateField K (PadicAlgCl p))
    [FiniteDimensional K E] [IsGalois K E] : ∃ S : Subgroup Eˣ,
    (∀ (σ : E ≃ₐ[K] E) (u v : Eˣ), u ∈ S → (v : E) = σ u → v ∈ S) ∧
    (∀ u ∈ S, ‖((u : E) : PadicAlgCl p)‖ = 1) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : Eˣ, ‖((u : E) : PadicAlgCl p) - 1‖ < ε → u ∈ S) ∧
    (∀ u ∈ S, (∀ σ : E ≃ₐ[K] E, σ (u : E) = u) → ∃ v ∈ S, ∏ σ : E ≃ₐ[K] E, σ (v : E) = u) ∧
    ∀ σ₀ : E ≃ₐ[K] E, (∀ σ, σ ∈ Subgroup.zpowers σ₀) → ∀ u ∈ S, ∏ σ : E ≃ₐ[K] E, σ (u : E) = 1 →
      ∃ v ∈ S, σ₀ (v : E) = u * v := by sorry
