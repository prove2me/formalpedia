-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_pow_degree_mem_normGroup
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.pow_degree_mem_normGroup
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:14.8998+00:00
-- url     : https://prove2.me/theorems/103542e1-0067-4b57-a6ec-fb67f84455a6
-- title:
--   Local Class Field: pow degree mem norm Group
-- statement:
--   The Local Class Field construction uses the pow degree mem norm Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L212-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L212-L215

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.pow_degree_mem_normGroup (h : K ≤ L) (x : Kˣ) : x ^ degLK p K L ∈ normGrp p K L := by sorry
