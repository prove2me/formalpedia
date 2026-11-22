-- Prove2me | Theorems.Thm_PI_OrbShared_Tri_IsTri_hasSubst
-- name    : PI.OrbShared.Tri.IsTri.hasSubst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:20.592079+00:00
-- url     : https://prove2.me/theorems/cf458dd7-e6da-417b-bd06-96de009a2d9b
-- title:
--   Is Tri: has Subst
-- statement:
--   The Is Tri construction uses the has Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L24-L25

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

theorem PI.OrbShared.Tri.IsTri.hasSubst (ha : IsTri c a) : HasSubst a := by sorry
