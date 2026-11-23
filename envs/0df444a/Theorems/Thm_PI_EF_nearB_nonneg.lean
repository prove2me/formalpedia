-- Prove2me | Theorems.Thm_PI_EF_nearB_nonneg
-- name    : PI.EF.nearB_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:49.470084+00:00
-- url     : https://prove2.me/theorems/ac1568d7-7a61-4005-8611-ecb28053e9e2
-- title:
--   EF: near B nonneg
-- statement:
--   The EF construction uses the near B nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L14-L24

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

theorem PI.EF.nearB_nonneg {u T : ℝ} (hu : 0 < u) (hT : 0 < T) (n : ℕ) : 0 ≤ nearB u T n := by sorry
