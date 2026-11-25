-- Prove2me | Theorems.Thm_PI_EF_mem_ball_ctr
-- name    : PI.EF.mem_ball_ctr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:52.704174+00:00
-- url     : https://prove2.me/theorems/ba6e2314-87c9-4b5b-a136-c348864bfa24
-- title:
--   EF: mem ball ctr
-- statement:
--   The EF construction uses the mem ball ctr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogWindowLe.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogWindowLe.lean#L30-L36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogWindowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]

theorem PI.EF.mem_ball_ctr (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3) :
    s ∈ closedBall (ctr s.im) (5 / 2) := by sorry
