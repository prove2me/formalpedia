-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_map_divHom_top
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.map_divHom_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:15.830355+00:00
-- url     : https://prove2.me/theorems/eaf689a4-cc25-45d7-871c-4ff310f1bd97
-- title:
--   Local Class Field: map div Hom top
-- statement:
--   The Local Class Field construction uses the map div Hom top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L26-L27

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.map_divHom_top (e : ℕ) : (⊤ : AddSubgroup ℤ).map (divHom e) = AddSubgroup.zmultiples ((e : ℝ)⁻¹) := by sorry
