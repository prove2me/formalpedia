-- Prove2me | Theorems.Thm_PI_ExpIntWProof_inv_nat_mem_Wf
-- name    : PI.ExpIntWProof.inv_nat_mem_Wf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:07.627218+00:00
-- url     : https://prove2.me/theorems/e2b6c5f8-6788-5b23-a766-3c38d2c3389e
-- title:
--   Exp Int WProof: inv nat mem Wf
-- statement:
--   The Exp Int WProof construction uses the inv nat mem Wf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatMemWf.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatMemWf.lean#L33-L40

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof
open PI

theorem PI.ExpIntWProof.inv_nat_mem_Wf (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : m ≠ 0) :
    ((m : ℂ_[p]))⁻¹ ∈ Wf p := by sorry
