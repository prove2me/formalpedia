-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_sup_eq_inf
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.subG_sup_eq_inf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:28:00.456409+00:00
-- url     : https://prove2.me/theorems/62c3fc58-393c-487e-ba1a-8b47b818aaff
-- title:
--   Local Class Field: sub G sup eq inf
-- statement:
--   The Local Class Field construction uses the sub G sup eq inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean#L27-L41

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.subG_sup_eq_inf (L L' : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    subG p K (L ⊔ L') = subG p K L ⊓ subG p K L' := by sorry
