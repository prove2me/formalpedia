-- Prove2me | Theorems.Thm_PI_Mk_term_eq
-- name    : PI.Mk.term_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:56.00795+00:00
-- url     : https://prove2.me/theorems/dd7dc086-6fa7-4e12-b7b0-ebe726b77722
-- title:
--   Mk: term eq
-- statement:
--   The Mk construction uses the term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/Assemble.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/Assemble.lean#L9-L10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Finset

theorem PI.Mk.term_eq (N p i : ℕ) : N / (p ^ i * (p - 1)) = (N / (p - 1)) / p ^ i := by sorry
