-- Prove2me | Theorems.Thm_PI_InvIdealIdxPiWork_idS_mono
-- name    : PI.InvIdealIdxPiWork.idS_mono
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:49.382811+00:00
-- url     : https://prove2.me/theorems/0b7dc2d4-baf0-4a1b-abb1-ebf7aa2e1f5e
-- title:
--   Inv Ideal Idx Pi Work: id S mono
-- statement:
--   The Inv Ideal Idx Pi Work construction uses the id S mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvertibleIdealIndex/SubmodulePiToAddSubgroup.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvertibleIdealIndex/SubmodulePiToAddSubgroup.lean#L47-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InvIdealIdxPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvertibleIdealIndex_SubmodulePiToAddSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvIdealIdxPiWork
open NumberField nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]

theorem PI.InvIdealIdxPiWork.idS_mono {I I' : Ideal (𝓞 E)} (h : I ≤ I') : idS (E := E) I ≤ idS I' := by sorry
