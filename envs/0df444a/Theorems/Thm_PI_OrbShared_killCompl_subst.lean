-- Prove2me | Theorems.Thm_PI_OrbShared_killCompl_subst
-- name    : PI.OrbShared.killCompl_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:56.03678+00:00
-- url     : https://prove2.me/theorems/03038d7f-3672-4e75-8d3a-2f7c89c69b59
-- title:
--   Orb Shared: kill Compl subst
-- statement:
--   The Orb Shared construction uses the kill Compl subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/KillSubst.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/KillSubst.lean#L33-L39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_KillSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OrbShared
open MvPowerSeries
open scoped MvPowerSeries.WithPiTopology
variable {σ τ υ R : Type*} [CommRing R]

theorem PI.OrbShared.killCompl_subst (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (f : MvPowerSeries σ R) :
    killCompl e (subst a f) = subst (fun s => killCompl e (a s)) f := by sorry
