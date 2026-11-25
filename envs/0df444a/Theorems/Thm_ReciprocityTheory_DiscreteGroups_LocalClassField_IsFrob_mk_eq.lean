-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrob_mk_eq
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrob.mk_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:57:28.072882+00:00
-- url     : https://prove2.me/theorems/0bdf1315-14c8-448b-9601-41f58a122091
-- title:
--   Is Frob: mk eq
-- statement:
--   The Is Frob construction uses the mk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L163-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L163-L165

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrob.mk_eq (hK : FiniteDimensional ℚ_[p] K) {σ : GK p K} (h : IsFrob p K σ) :
    (QuotientGroup.mk σ : GalLK p K (MaximalUnramifiedExtension p K)) = frobLK p K (MaximalUnramifiedExtension p K) := by sorry
