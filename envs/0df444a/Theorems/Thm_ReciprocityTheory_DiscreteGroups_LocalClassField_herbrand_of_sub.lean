-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_herbrand_of_sub
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.herbrand_of_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:55:29.729984+00:00
-- url     : https://prove2.me/theorems/f396a097-3303-50fb-aab4-050fa490a359
-- title:
--   Local Class Field: herbrand of sub
-- statement:
--   The Local Class Field construction uses the herbrand of sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrand.lean#L141-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrand.lean#L141-L196

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Herbrand
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrand
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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.herbrand_of_sub {G M : Type*} [Group G] [Fintype G] [AddCommGroup M] (ρ : Representation ℤ G M) (g₀ : G)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (W : Submodule ℤ M) (hW1 : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hW2 : W.toAddSubgroup.FiniteIndex)
    (hW3 : ∀ w ∈ W, (∀ g, ρ g w = w) → ∃ w' ∈ W, ∑ g, ρ g w' = w)
    (hW4 : ∀ w ∈ W, ∑ g, ρ g w = 0 → ∃ w' ∈ W, ρ g₀ w' - w' = w) :
    Herbrand.HFin ρ g₀ ∧ Herbrand.h ρ g₀ = 1 := by sorry
