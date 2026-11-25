-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_eK_Kur
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.eK_Kur
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:02:52.394802+00:00
-- url     : https://prove2.me/theorems/2e8efae0-5cfb-5eb0-bf88-1f71e57b8f45
-- title:
--   Local Class Field: e K Kur
-- statement:
--   The Local Class Field construction uses the e K Kur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L33-L36

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
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
variable (p : ℕ) [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.eK_Kur (hK : FiniteDimensional ℚ_[p] K) : eK p (MaximalUnramifiedExtension p K) = eK p K := by sorry
