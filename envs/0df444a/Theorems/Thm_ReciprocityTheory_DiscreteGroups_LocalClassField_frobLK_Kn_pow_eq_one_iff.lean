-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_frobLK_Kn_pow_eq_one_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.frobLK_Kn_pow_eq_one_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:06:59.944934+00:00
-- url     : https://prove2.me/theorems/389ca19b-1a91-51e3-b636-6b06851d4e72
-- title:
--   Local Class Field: frob LK Kn pow eq one iff
-- statement:
--   The Local Class Field construction uses the frob LK Kn pow eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L210-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L210-L214

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
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
variable {p K}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.frobLK_Kn_pow_eq_one_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    frobLK p K (Kn p K n) ^ i = 1 ↔ n ∣ i := by sorry
