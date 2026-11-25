-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_sep_of_mem
-- name    : PI.UnitaryGroupMassFormula.PolyCoef.sep_of_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:32:38.213521+00:00
-- url     : https://prove2.me/theorems/602a7203-917f-4c1b-a927-d67ef3e0e623
-- title:
--   Poly Coef: sep of mem
-- statement:
--   The Poly Coef construction uses the sep of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L163-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L163-L178

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

theorem PI.UnitaryGroupMassFormula.PolyCoef.sep_of_mem {N : ℕ} {f : C(UG N, ℂ)} (hf : f ∈ algA N) : Sep (⇑f) := by sorry
