-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_pow_card_minpoly
-- name    : PI.SqfRootsInj.W.pow_card_minpoly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:16.036348+00:00
-- url     : https://prove2.me/theorems/825370d5-7a02-4946-8df2-ece6c49ff952
-- title:
--   W: pow card minpoly
-- statement:
--   The W construction uses the pow card minpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitBase.lean#L45-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitBase.lean#L45-L59

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
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
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab

theorem PI.SqfRootsInj.W.pow_card_minpoly {g : ℕ} [Fact g.Prime] (w : Fbar g) :
    w ^ (g ^ (minpoly (ZMod g) w).natDegree) = w := by sorry
