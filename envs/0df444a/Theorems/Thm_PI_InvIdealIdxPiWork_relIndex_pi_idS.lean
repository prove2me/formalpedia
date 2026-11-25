-- Prove2me | Theorems.Thm_PI_InvIdealIdxPiWork_relIndex_pi_idS
-- name    : PI.InvIdealIdxPiWork.relIndex_pi_idS
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:14.087949+00:00
-- url     : https://prove2.me/theorems/fd7eba08-8955-59ea-9ef4-3e75ceda917b
-- title:
--   Inv Ideal Idx Pi Work: rel Index pi id S
-- statement:
--   The Inv Ideal Idx Pi Work construction uses the rel Index pi id S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvertibleIdealIndex/SubmodulePiToAddSubgroup.lean#L70-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvertibleIdealIndex/SubmodulePiToAddSubgroup.lean#L70-L87

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

theorem PI.InvIdealIdxPiWork.relIndex_pi_idS {ι : Type} [Fintype ι] (I : ι → Ideal (𝓞 E)) :
    (AddSubgroup.pi Set.univ (fun i => idS (I i))).relIndex
      (AddSubgroup.pi Set.univ (fun _ : ι => idS (E := E) ⊤)) = ∏ i, Ideal.absNorm (I i) := by sorry
