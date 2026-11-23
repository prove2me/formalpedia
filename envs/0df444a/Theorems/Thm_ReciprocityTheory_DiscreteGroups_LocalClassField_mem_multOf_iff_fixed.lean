-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_multOf_iff_fixed
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.mem_multOf_iff_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:55:07.126213+00:00
-- url     : https://prove2.me/theorems/48b95769-8e6f-497a-9c06-44131c6d33b3
-- title:
--   Local Class Field: mem mult Of iff fixed
-- statement:
--   The Local Class Field construction uses the mem mult Of iff fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L244-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L244-L249

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
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
variable {p K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.mem_multOf_iff_fixed (h : K ≤ L) (x : KbarMult p) :
    x ∈ multOf p L ↔ ∀ σ ∈ subG p K L, kbarRep p K σ x = x := by sorry
