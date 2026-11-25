-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_coord
-- name    : PI.UnitaryGroupMassFormula.PolyCoef.Sep.coord
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:52:49.810938+00:00
-- url     : https://prove2.me/theorems/a8a74da0-3c3f-4c74-8130-851830bc532d
-- title:
--   Sep: coord
-- statement:
--   The Sep construction uses the coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L146-L152

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory Matrix

theorem PI.UnitaryGroupMassFormula.PolyCoef.Sep.coord {N : ℕ} (i j : Fin N) : Sep (fun g : UG N => (g : Matrix (Fin N) (Fin N) ℂ) i j) := by sorry
