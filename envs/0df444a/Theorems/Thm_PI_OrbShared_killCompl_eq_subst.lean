-- Prove2me | Theorems.Thm_PI_OrbShared_killCompl_eq_subst
-- name    : PI.OrbShared.killCompl_eq_subst
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:35:30.506317+00:00
-- url     : https://prove2.me/theorems/efea12bc-81ff-5ba3-9c19-914c6b07a0ec
-- title:
--   Orb Shared: kill Compl eq subst
-- statement:
--   The Orb Shared construction uses the kill Compl eq subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/KillSubst.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/KillSubst.lean#L41-L45

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

theorem PI.OrbShared.killCompl_eq_subst (e : υ ↪ τ) (f : MvPowerSeries τ R) :
    killCompl e f = subst (fun t => killCompl e (X t : MvPowerSeries τ R)) f := by sorry
