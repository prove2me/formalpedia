-- Prove2me | Theorems.Thm_PI_BesselDerivW_liftA_apply
-- name    : PI.BesselDerivW.liftA_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:44:09.472436+00:00
-- url     : https://prove2.me/theorems/28767383-39a1-5b05-865d-524fc21179d4
-- title:
--   Bessel Deriv W: lift A apply
-- statement:
--   The Bessel Deriv W construction uses the lift A apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselDerivatives/LiftAOneZero.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselDerivatives/LiftAOneZero.lean#L14-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_LiftAOneZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
noncomputable section
open PI PI.BesselDerivW
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem PI.BesselDerivW.liftA_apply (a : E →L[ℝ] E) (p : ℝ × E) : liftA a p = (0, a p.2) := by sorry
