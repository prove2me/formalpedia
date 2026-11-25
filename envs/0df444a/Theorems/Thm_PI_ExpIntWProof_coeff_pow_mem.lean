-- Prove2me | Theorems.Thm_PI_ExpIntWProof_coeff_pow_mem
-- name    : PI.ExpIntWProof.coeff_pow_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:31.870946+00:00
-- url     : https://prove2.me/theorems/388a2f01-1df7-42db-911a-8be53a20a1de
-- title:
--   Exp Int WProof: coeff pow mem
-- statement:
--   The Exp Int WProof construction uses the coeff pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatMemWf.lean#L42-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatMemWf.lean#L42-L56

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

theorem PI.ExpIntWProof.coeff_pow_mem {σ : Type} (p : ℕ) [Fact p.Prime] (f : MvPowerSeries σ ℂ_[p])
    (hf : CoefWf f) : ∀ n : ℕ, ∀ α, MvPowerSeries.coeff α (f ^ n) ∈ Wf p := by sorry
