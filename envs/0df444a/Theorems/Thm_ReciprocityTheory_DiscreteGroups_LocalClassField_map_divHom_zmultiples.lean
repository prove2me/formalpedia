-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_map_divHom_zmultiples
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.map_divHom_zmultiples
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:10.038424+00:00
-- url     : https://prove2.me/theorems/29884882-2046-4c77-b742-e800cfa003e0
-- title:
--   Local Class Field: map div Hom zmultiples
-- statement:
--   The Local Class Field construction uses the map div Hom zmultiples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L19-L24

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.map_divHom_zmultiples {e : ℕ} (he : 0 < e) :
    (AddSubgroup.zmultiples (e : ℤ)).map (divHom e) = AddSubgroup.zmultiples (1 : ℝ) := by sorry
