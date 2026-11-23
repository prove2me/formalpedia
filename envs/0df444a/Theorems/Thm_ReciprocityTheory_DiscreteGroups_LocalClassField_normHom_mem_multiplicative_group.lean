-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_normHom_mem_multiplicative_group
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_mem_multiplicative_group
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:00.014155+00:00
-- url     : https://prove2.me/theorems/a940d972-e9d4-4fa8-ad81-c1df4aa38e3c
-- title:
--   Local Class Field: norm Hom mem multiplicative group
-- statement:
--   The Local Class Field construction uses the norm Hom mem multiplicative group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L56-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L56-L67

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_mem_multiplicative_group (hL : FiniteDimensional ℚ_[p] L) (y : KbarMult p) (hy : y ∈ multOf p L) :
    normHom p K L y ∈ multOf p K := by sorry
