-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_algebraNorm
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.norm_algebraNorm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:53:27.108529+00:00
-- url     : https://prove2.me/theorems/9ce83a4f-1ee2-5e42-b284-d91c7481c21b
-- title:
--   Local Class Field: norm algebra Norm
-- statement:
--   The Local Class Field construction uses the norm algebra Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsA.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsA.lean#L76-L84

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
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
variable {K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.norm_algebraNorm (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : IntermediateField.extendScalars h) :
    ‖((Algebra.norm K x : K) : PadicAlgCl p)‖ =
      ‖(x : PadicAlgCl p)‖ ^ Module.finrank K (IntermediateField.extendScalars h) := by sorry
