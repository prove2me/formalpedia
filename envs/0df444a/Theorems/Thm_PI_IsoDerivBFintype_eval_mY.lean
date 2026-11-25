-- Prove2me | Theorems.Thm_PI_IsoDerivBFintype_eval_mY
-- name    : PI.IsoDerivBFintype.eval_mY
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:08:54.321554+00:00
-- url     : https://prove2.me/theorems/6f562e2d-686c-4a3b-a82e-3a306e79c10f
-- title:
--   Iso Deriv BFintype: eval m Y
-- statement:
--   The Iso Deriv BFintype construction uses the eval m Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean#L82-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean#L82-L93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.IsoDerivBFintype
open PI.IsoDerivB
variable {Lt T : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) {N N' : ℕ}
  (nu : Lt → YoungDiagram)

theorem PI.IsoDerivBFintype.eval_mY (J : ColChoice N nu) (y : T → Matrix (Fin N) (Fin N) ℂ) :
    MvPolynomial.eval (fun k : FrV T N => y k.1 k.2.1 k.2.2) (mY tp nu J) = minY N nu J (frC tp y) := by sorry
