-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_adjugate_eq
-- name    : PI.UnitaryGroupMassFormula.PolyCoef.adjugate_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:12.160008+00:00
-- url     : https://prove2.me/theorems/ee40ac78-a5d1-5cff-86e2-9302c305da94
-- title:
--   Poly Coef: adjugate eq
-- statement:
--   The Poly Coef construction uses the adjugate eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L77-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L77-L87

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

theorem PI.UnitaryGroupMassFormula.PolyCoef.adjugate_eq {N : ℕ} (g : UG N) :
    (g : Matrix (Fin N) (Fin N) ℂ).adjugate =
      (g : Matrix (Fin N) (Fin N) ℂ).det • star (g : Matrix (Fin N) (Fin N) ℂ) := by sorry
