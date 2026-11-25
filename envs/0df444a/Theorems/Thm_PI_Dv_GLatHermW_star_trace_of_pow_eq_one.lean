-- Prove2me | Theorems.Thm_PI_Dv_GLatHermW_star_trace_of_pow_eq_one
-- name    : PI.Dv.GLatHermW.star_trace_of_pow_eq_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:15.888529+00:00
-- url     : https://prove2.me/theorems/30353c4e-d67a-4213-96a3-9d592fea5423
-- title:
--   GLat Herm W: star trace of pow eq one
-- statement:
--   The GLat Herm W construction uses the star trace of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/StarMapTraceOfPowEqOne.lean#L11-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/StarMapTraceOfPowEqOne.lean#L11-L45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_StarMapTraceOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLatHermW
open Matrix
open scoped ComplexOrder

theorem PI.Dv.GLatHermW.star_trace_of_pow_eq_one {d : Type} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) (n : ℕ) (hn : 0 < n) (hA : A ^ n = 1) :
    star A.trace = (A ^ (n - 1)).trace := by sorry
