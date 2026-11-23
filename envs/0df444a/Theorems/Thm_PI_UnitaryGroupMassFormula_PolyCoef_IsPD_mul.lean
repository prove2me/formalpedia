-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_mul
-- name    : PI.UnitaryGroupMassFormula.PolyCoef.IsPD.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:07.487505+00:00
-- url     : https://prove2.me/theorems/e8f53dd5-81be-46bd-852e-2d604a9b1725
-- title:
--   Is PD: mul
-- statement:
--   The Is PD construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L63-L68

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

theorem PI.UnitaryGroupMassFormula.PolyCoef.IsPD.mul {N : ℕ} {f f' : UG N → ℂ} (hf : IsPD f) (hf' : IsPD f') : IsPD (fun g => f g * f' g) := by sorry
