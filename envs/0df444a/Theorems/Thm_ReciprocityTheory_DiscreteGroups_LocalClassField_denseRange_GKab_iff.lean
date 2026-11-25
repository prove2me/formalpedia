-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_denseRange_GKab_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.denseRange_GKab_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:53:12.194521+00:00
-- url     : https://prove2.me/theorems/ce73b4e2-fce8-516b-9501-5cfe15c74d49
-- title:
--   Local Class Field: dense Range GKab iff
-- statement:
--   The Local Class Field construction uses the dense Range GKab iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean#L183-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean#L183-L204

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.denseRange_GKab_iff (hK : FiniteDimensional ℚ_[p] K) {X : Type*} (f : X → GKab p K) :
    DenseRange f ↔ ∀ L, IsAbLK p K L → ∀ g : GK p K, ∃ (x : X) (g' : GK p K), toAbK p K g' = f x ∧
      g'⁻¹ * g ∈ subG p K L := by sorry
