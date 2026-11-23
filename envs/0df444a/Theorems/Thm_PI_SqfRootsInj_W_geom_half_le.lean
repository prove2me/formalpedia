-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_geom_half_le
-- name    : PI.SqfRootsInj.W.geom_half_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:55.561572+00:00
-- url     : https://prove2.me/theorems/93661c49-045c-4e17-a4fe-0942971ef664
-- title:
--   W: geom half le
-- statement:
--   The W construction uses the geom half le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/SumSqPowLeTwo.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/SumSqPowLeTwo.lean#L13-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo
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
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab

theorem PI.SqfRootsInj.W.geom_half_le (k n : ℕ) : ∑ e ∈ Finset.Icc k n, (1 / 2 : ℝ) ^ (e - k) ≤ 2 := by sorry
