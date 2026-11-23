-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_normHom_apply
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:01.328681+00:00
-- url     : https://prove2.me/theorems/1a8c3656-1b3a-4400-a9e9-5bebd85bd033
-- title:
--   Local Class Field: norm Hom apply
-- statement:
--   The Local Class Field construction uses the norm Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L11-L15

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
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
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_apply [Fintype (GK p K ⧸ subG p K L)] (y : KbarMult p) :
    normHom p K L y = ∑ c : GK p K ⧸ subG p K L, kbarRep p K c.out y := by sorry
