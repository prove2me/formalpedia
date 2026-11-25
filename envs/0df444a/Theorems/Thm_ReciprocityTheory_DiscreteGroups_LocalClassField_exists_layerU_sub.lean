-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_layerU_sub
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.exists_layerU_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:30.463174+00:00
-- url     : https://prove2.me/theorems/8b8f70aa-8fd3-5a16-ab64-67a040cc04c1
-- title:
--   Local Class Field: exists layer U sub
-- statement:
--   The Local Class Field construction uses the exists layer U sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrand.lean#L55-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrand.lean#L55-L139

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.exists_layerU_sub (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] :
    ∃ W : Submodule ℤ (layerU p K L).V, (∀ g, ∀ w ∈ W, (layerU p K L).rho g w ∈ W) ∧
      W.toAddSubgroup.FiniteIndex ∧
      (∀ w ∈ W, (∀ g, (layerU p K L).rho g w = w) → ∃ w' ∈ W, ∑ g, (layerU p K L).rho g w' = w) ∧
      ∀ g₀ : GalLK p K L, (∀ g, g ∈ Subgroup.zpowers g₀) → ∀ w ∈ W, ∑ g, (layerU p K L).rho g w = 0 →
        ∃ w' ∈ W, (layerU p K L).rho g₀ w' - w' = w := by sorry
