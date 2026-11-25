-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrob_pow_apply
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrob.pow_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:55:44.002777+00:00
-- url     : https://prove2.me/theorems/4f019e7c-7033-416d-822c-d86bddcdee2a
-- title:
--   Is Frob: pow apply
-- statement:
--   The Is Frob construction uses the pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L305-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L305-L310

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrob.pow_apply (hK : FiniteDimensional ℚ_[p] K) {σ : GK p K} (h : IsFrob p K σ) {m : ℕ}
    (hm : ¬ p ∣ m) (i : ℕ) {ζ : PadicAlgCl p} (hζ : ζ ^ m = 1) : (σ ^ i) ζ = ζ ^ (qK p K ^ i) := by sorry
