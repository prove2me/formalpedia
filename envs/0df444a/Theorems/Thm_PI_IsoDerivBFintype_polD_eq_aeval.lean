-- Prove2me | Theorems.Thm_PI_IsoDerivBFintype_polD_eq_aeval
-- name    : PI.IsoDerivBFintype.polD_eq_aeval
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:47.361874+00:00
-- url     : https://prove2.me/theorems/e5eeb905-a997-4c8d-8f18-fc025b8cecc4
-- title:
--   Iso Deriv BFintype: pol D eq aeval
-- statement:
--   The Iso Deriv BFintype construction uses the pol D eq aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/IsoDerivB.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/IsoDerivB.lean#L22-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_IsoDerivB
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
variable {T : Type} {N N' : ℕ} (s : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ)

theorem PI.IsoDerivBFintype.polD_eq_aeval (Q : MvPolynomial (FrV T N) ℂ) :
    polD s Q y' = MvPolynomial.aeval (gD s y') Q := by sorry
