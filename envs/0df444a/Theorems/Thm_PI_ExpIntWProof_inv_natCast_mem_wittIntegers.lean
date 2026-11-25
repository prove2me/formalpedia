-- Prove2me | Theorems.Thm_PI_ExpIntWProof_inv_natCast_mem_wittIntegers
-- name    : PI.ExpIntWProof.inv_natCast_mem_wittIntegers
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:39.9448+00:00
-- url     : https://prove2.me/theorems/7852dc20-be1d-5223-9069-f5a4991c26e1
-- title:
--   Exp Int WProof: inv nat Cast mem witt Integers
-- statement:
--   The Exp Int WProof construction uses the inv nat Cast mem witt Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatCastMemWittIntegers.lean#L30-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatCastMemWittIntegers.lean#L30-L61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
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

theorem PI.ExpIntWProof.inv_natCast_mem_wittIntegers (p : ℕ) [hp : Fact p.Prime] (u : ℕ) (hu : ¬ p ∣ u) :
    ((u : ℂ_[p]))⁻¹ ∈ Wp p := by sorry
