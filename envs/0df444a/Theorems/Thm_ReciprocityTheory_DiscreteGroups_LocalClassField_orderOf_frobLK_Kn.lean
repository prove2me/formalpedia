-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_orderOf_frobLK_Kn
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.orderOf_frobLK_Kn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:00:46.948876+00:00
-- url     : https://prove2.me/theorems/7ec0ac5f-5a93-5953-9757-2b01d741aca5
-- title:
--   Local Class Field: order Of frob LK Kn
-- statement:
--   The Local Class Field construction uses the order Of frob LK Kn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L216-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L216-L220

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.orderOf_frobLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    orderOf (frobLK p K (Kn p K n)) = n := by sorry
