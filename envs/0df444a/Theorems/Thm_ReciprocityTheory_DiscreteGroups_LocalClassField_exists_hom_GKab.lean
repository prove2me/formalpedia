-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_hom_GKab
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.exists_hom_GKab
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:40.326103+00:00
-- url     : https://prove2.me/theorems/460fb2f9-e962-4298-a22d-62c1dc285bd5
-- title:
--   Local Class Field: exists hom GKab
-- statement:
--   The Local Class Field construction uses the exists hom GKab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean#L206-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean#L206-L224

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
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
open Topology
open scoped commutatorElement
variable {p K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.exists_hom_GKab (hK : FiniteDimensional ℚ_[p] K) {A : Type*} [Group A] (γ : IntermediateField ℚ_[p] (PadicAlgCl p) → A → GK p K)
    (hmul : ∀ L, IsAbLK p K L → ∀ a b, (γ L (a * b))⁻¹ * (γ L a * γ L b) ∈ subG p K L)
    (hγ : ∀ L L', IsAbLK p K L → IsAbLK p K L' → L ≤ L' → ∀ a, (γ L a)⁻¹ * γ L' a ∈ subG p K L) :
    ∃ f : A →* GKab p K, ∀ L, IsAbLK p K L → ∀ (a : A) (g : GK p K), toAbK p K g = f a →
      (γ L a)⁻¹ * g ∈ subG p K L := by sorry
