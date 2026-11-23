-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_normGrp_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.mem_normGrp_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:46:54.562721+00:00
-- url     : https://prove2.me/theorems/3aa72440-d58c-4b56-9c31-7b2cd729e2a6
-- title:
--   Local Class Field: mem norm Grp iff
-- statement:
--   The Local Class Field construction uses the mem norm Grp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecDefs.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecDefs.lean#L28-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.mem_normGrp_iff (x : Kˣ) :
    x ∈ normGrp p K L ↔ ∃ y ∈ multOf p L, normHom p K L y = ofK p K (Additive.ofMul x) := by sorry
