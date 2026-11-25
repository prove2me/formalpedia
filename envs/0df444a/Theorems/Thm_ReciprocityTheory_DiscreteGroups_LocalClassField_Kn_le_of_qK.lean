-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kn_le_of_qK
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Kn_le_of_qK
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:05.278582+00:00
-- url     : https://prove2.me/theorems/d6077646-e723-45ad-9d98-716b637f6d02
-- title:
--   Local Class Field: Kn le of q K
-- statement:
--   The Local Class Field construction uses the Kn le of q K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L57-L66

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Kn_le_of_qK (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) {n m : ℕ} (h : qK p L = qK p K ^ (n * m)) :
    Kn p K n ≤ L := by sorry
