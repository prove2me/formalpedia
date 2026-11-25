-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isZHat_GalKur
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.isZHat_GalKur
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:11:27.599849+00:00
-- url     : https://prove2.me/theorems/bc59b0d2-6e2b-4c96-8baf-babb432f797b
-- title:
--   Local Class Field: is ZHat Gal Kur
-- statement:
--   The Local Class Field construction uses the is ZHat Gal Kur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L234-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L234-L277

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.isZHat_GalKur (hK : FiniteDimensional ℚ_[p] K) :
    IsZHat (GalLK p K (MaximalUnramifiedExtension p K)) (frobLK p K (MaximalUnramifiedExtension p K)) := by sorry
