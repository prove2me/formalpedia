-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_g_pow_sub_one_ne
-- name    : PI.SqfRootsInj.W.g_pow_sub_one_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:47.634831+00:00
-- url     : https://prove2.me/theorems/551bfd8c-d5a8-44ae-bac7-1bb74ced5424
-- title:
--   W: g pow sub one ne
-- statement:
--   The W construction uses the g pow sub one ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/CardLeSumOfCover.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/CardLeSumOfCover.lean#L50-L52

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_DivCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
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

theorem PI.SqfRootsInj.W.g_pow_sub_one_ne {g e : ℕ} (hg2 : 1 < g) (he : 1 ≤ e) : g ^ e - 1 ≠ 0 := by sorry
