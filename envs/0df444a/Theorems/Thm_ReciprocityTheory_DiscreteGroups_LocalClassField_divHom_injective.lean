-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_divHom_injective
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.divHom_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:42.756001+00:00
-- url     : https://prove2.me/theorems/654716fd-0ce2-4515-9b7b-df8a082a0f77
-- title:
--   Local Class Field: div Hom injective
-- statement:
--   The Local Class Field construction uses the div Hom injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L13-L17

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.divHom_injective {e : ℕ} (he : 0 < e) : Function.Injective (divHom e) := by sorry
