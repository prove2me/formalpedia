-- Prove2me | Theorems.Thm_PI_InvIdealIdxPiWork_submodule_pi_toAddSubgroup
-- name    : PI.InvIdealIdxPiWork.submodule_pi_toAddSubgroup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:44.340199+00:00
-- url     : https://prove2.me/theorems/2ca2c15e-ca23-498c-b950-9bd44a2314eb
-- title:
--   Inv Ideal Idx Pi Work: submodule pi to Add Subgroup
-- statement:
--   The Inv Ideal Idx Pi Work construction uses the submodule pi to Add Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvertibleIdealIndex/SubmodulePiToAddSubgroup.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvertibleIdealIndex/SubmodulePiToAddSubgroup.lean#L29-L34

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

theorem PI.InvIdealIdxPiWork.submodule_pi_toAddSubgroup {ι : Type} {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : ι → Submodule R M) :
    (Submodule.pi Set.univ p).toAddSubgroup =
      AddSubgroup.pi Set.univ (fun i => (p i).toAddSubgroup) := by sorry
