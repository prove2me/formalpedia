-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_mapX_eval
-- name    : PI.UnitaryGroupMassFormula.PolyCoef.mapX_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:45:39.943828+00:00
-- url     : https://prove2.me/theorems/9ea7a293-d70e-4524-9094-5e4241fa20d2
-- title:
--   Poly Coef: map X eval
-- statement:
--   The Poly Coef construction uses the map X eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L43-L46

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

theorem PI.UnitaryGroupMassFormula.PolyCoef.mapX_eval {N : ℕ} (g : UG N) :
    (MvPolynomial.eval (ent g)).mapMatrix (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ) =
      (g : Matrix (Fin N) (Fin N) ℂ) := by sorry
