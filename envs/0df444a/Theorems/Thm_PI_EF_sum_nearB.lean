-- Prove2me | Theorems.Thm_PI_EF_sum_nearB
-- name    : PI.EF.sum_nearB
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:53.408803+00:00
-- url     : https://prove2.me/theorems/d39b33e3-09c0-4fa3-9fd7-375634e0315b
-- title:
--   EF: sum near B
-- statement:
--   The EF construction uses the sum near B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L35-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L35-L72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound
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
open Finset

theorem PI.EF.sum_nearB (u T : ℝ) :
    ∑ n ∈ range (⌊u⌋₊ + (⌊u⌋₊ + 2)), nearB u T n =
      4 + 2 * ((4 * u / T) * ∑ j ∈ range ⌊u⌋₊, 1 / ((j : ℝ) + 1)) := by sorry
