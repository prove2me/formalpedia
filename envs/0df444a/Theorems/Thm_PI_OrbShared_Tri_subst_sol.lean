-- Prove2me | Theorems.Thm_PI_OrbShared_Tri_subst_sol
-- name    : PI.OrbShared.Tri.subst_sol
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:35.387153+00:00
-- url     : https://prove2.me/theorems/010a4f36-6c8b-4a69-b3f2-f346dd7ef348
-- title:
--   Tri: subst sol
-- statement:
--   The Tri construction uses the subst sol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L189-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L189-L202

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange
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
open PI PI.OrbShared PI.OrbShared.Tri
open MvPowerSeries Finsupp
variable {K : Type*} [Field K] {σ : Type*} [Finite σ]
variable {c : K} {a : σ → MvPowerSeries σ K}

theorem PI.OrbShared.Tri.subst_sol (hc : c ≠ 0) (ha : IsTri c a) (G : MvPowerSeries σ K) : subst a (sol c a G) = G := by sorry
