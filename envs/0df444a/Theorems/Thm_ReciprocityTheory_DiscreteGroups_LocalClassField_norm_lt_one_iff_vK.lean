-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_lt_one_iff_vK
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.norm_lt_one_iff_vK
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:00:40.1098+00:00
-- url     : https://prove2.me/theorems/53cb3ad9-02e6-5365-bd25-2a5f770f2a43
-- title:
--   Local Class Field: norm lt one iff v K
-- statement:
--   The Local Class Field construction uses the norm lt one iff v K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean#L62-L63

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.norm_lt_one_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ < 1 ↔ 1 ≤ vK p K x := by sorry
