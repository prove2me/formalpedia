-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_ptp_pow
-- name    : PI.SqfRootShift.W.ptp_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:41.264418+00:00
-- url     : https://prove2.me/theorems/8f84df01-faa2-4ed0-9953-b81fef733811
-- title:
--   W: ptp pow
-- statement:
--   The W construction uses the ptp pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountA.lean#L11-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountA.lean#L11-L36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab

theorem PI.SqfRootShift.W.ptp_pow {M : Type*} [Monoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x : M) (hx : 0 < orderOf x) :
    x ^ (ℓ ^ (orderOf x).factorization ℓ) =
      (primeToPart ℓ x) ^ (ℓ ^ (orderOf x).factorization ℓ) := by sorry
