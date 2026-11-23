-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_toAbK_eq_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.toAbK_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:13.699528+00:00
-- url     : https://prove2.me/theorems/a9ae9c45-2d58-4e52-89e6-54c0fd5f26c9
-- title:
--   Local Class Field: to Ab K eq iff
-- statement:
--   The Local Class Field construction uses the to Ab K eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean#L96-L99

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.toAbK_eq_iff (hK : FiniteDimensional ℚ_[p] K) (g g' : GK p K) :
    toAbK p K g = toAbK p K g' ↔ ∀ L, IsAbLK p K L → g⁻¹ * g' ∈ subG p K L := by sorry
