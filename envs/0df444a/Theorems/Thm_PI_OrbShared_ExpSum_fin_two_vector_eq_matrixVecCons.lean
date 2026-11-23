-- Prove2me | Theorems.Thm_PI_OrbShared_ExpSum_fin_two_vector_eq_matrixVecCons
-- name    : PI.OrbShared.ExpSum.fin_two_vector_eq_matrixVecCons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:41.79848+00:00
-- url     : https://prove2.me/theorems/2f1fec40-fe0c-4374-828e-dbcb763b6770
-- title:
--   Exp Sum: fin two vector eq matrix Vec Cons
-- statement:
--   The Exp Sum construction uses the fin two vector eq matrix Vec Cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L16-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.OrbShared PI.OrbShared.ExpSum
open MvPowerSeries
variable {K : Type*} [Field K] [CharZero K]

theorem PI.OrbShared.ExpSum.fin_two_vector_eq_matrixVecCons (e : Fin 2 →₀ ℕ) (k j : ℕ) :
    e = Finsupp.single 0 k + Finsupp.single 1 j ↔ e 0 = k ∧ e 1 = j := by sorry
