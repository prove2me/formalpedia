-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_geom_part
-- name    : PI.SqfRootShift.W.geom_part
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:27:05.829919+00:00
-- url     : https://prove2.me/theorems/8e485bef-6901-57fb-a35b-c6cbfd8f77e3
-- title:
--   W: geom part
-- statement:
--   The W construction uses the geom part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/ArithP.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/ArithP.lean#L9-L22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_ArithP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W

theorem PI.SqfRootShift.W.geom_part (G : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r - k) = G ^ (r - 1) - 1 := by sorry
