-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_eval_detP
-- name    : PI.UnitaryGroupMassFormula.PolyCoef.eval_detP
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:32:24.987811+00:00
-- url     : https://prove2.me/theorems/1be423e1-47d2-5641-b795-83f027da8802
-- title:
--   Poly Coef: eval det P
-- statement:
--   The Poly Coef construction uses the eval det P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L48-L51

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

theorem PI.UnitaryGroupMassFormula.PolyCoef.eval_detP {N : ℕ} (g : UG N) :
    MvPolynomial.eval (ent g) (detP N) = (g : Matrix (Fin N) (Fin N) ℂ).det := by sorry
