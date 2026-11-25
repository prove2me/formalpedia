-- Prove2me | Theorems.Thm_PI_Dv_GLPTr_star_trace_of_pow_eq_one
-- name    : PI.Dv.GLPTr.star_trace_of_pow_eq_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:28.009956+00:00
-- url     : https://prove2.me/theorems/54cfda3b-01e0-4983-b534-58517095d535
-- title:
--   GLPTr: star trace of pow eq one
-- statement:
--   The GLPTr construction uses the star trace of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/StarMapTraceOfPowEqOne.lean#L11-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/StarMapTraceOfPowEqOne.lean#L11-L45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_StarMapTraceOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLPTr
open Matrix
open scoped ComplexOrder

theorem PI.Dv.GLPTr.star_trace_of_pow_eq_one {d : Type} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) (n : ℕ) (hn : 0 < n) (hA : A ^ n = 1) :
    star A.trace = (A ^ (n - 1)).trace := by sorry
