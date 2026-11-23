-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_le_max__b9ad733dbc67
-- name    : P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_le_max__b9ad733dbc67
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:29.752659+00:00
-- url     : https://prove2.me/theorems/9938d4a6-3e7e-41a6-8fce-86356d739303
-- title:
--   P2 M Reciprocity Theory Discrete Groups Local Class Field Unramified Extensions norm sub le max  b9ad733dbc67: P2 M Reciprocity Theory Discrete Groups Local Class Field Unramified Extensions norm sub
-- statement:
--   The P2 M Reciprocity Theory Discrete Groups Local Class Field Unramified Extensions norm sub le max  b9ad733dbc67 construction uses the P2 M Reciprocity Theory Discrete Groups Local Class Field Unramified Extensions norm sub le max  b9ad733dbc67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormSubEqOneOfPowEqOne.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormSubEqOneOfPowEqOne.lean#L16-L17

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
import Definitions.Def_Lemmata_PadicNatCastNorm_NormNatCastOfNotDvd
import Definitions.Def_Lemmata_FirstBlockLemmaC_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaD_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField
variable {p : ℕ} [Fact p.Prime]

theorem P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_le_max__b9ad733dbc67 (x y : PadicAlgCl p) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by sorry

alias «ReciprocityTheory».«DiscreteGroups».«LocalClassField».«UnramifiedExtensions».«norm_sub_le_max'» := P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_le_max__b9ad733dbc67
