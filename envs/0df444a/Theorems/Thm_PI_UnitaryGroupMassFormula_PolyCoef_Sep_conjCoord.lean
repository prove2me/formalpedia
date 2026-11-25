-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_conjCoord
-- name    : PI.UnitaryGroupMassFormula.PolyCoef.Sep.conjCoord
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:06.58155+00:00
-- url     : https://prove2.me/theorems/05d4b82b-4ad3-51ae-8e73-5479f6fefb09
-- title:
--   Sep: conj Coord
-- statement:
--   The Sep construction uses the conj Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L154-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L154-L161

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

theorem PI.UnitaryGroupMassFormula.PolyCoef.Sep.conjCoord {N : ℕ} (i j : Fin N) :
    Sep (fun g : UG N => star ((g : Matrix (Fin N) (Fin N) ℂ) i j)) := by sorry
