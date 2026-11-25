-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_natDegree_minpoly_le
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.natDegree_minpoly_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:55:33.854723+00:00
-- url     : https://prove2.me/theorems/cd5289df-04b0-47a6-ac27-5127ed6e37cf
-- title:
--   Local Class Field: nat Degree minpoly le
-- statement:
--   The Local Class Field construction uses the nat Degree minpoly le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtC.lean#L42-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtC.lean#L42-L58

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Polynomial
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.natDegree_minpoly_le (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {ζ : PadicAlgCl p}
    (hζ : ζ ^ (qK p K ^ n - 1) = 1) : (minpoly K ζ).natDegree ≤ n := by sorry
