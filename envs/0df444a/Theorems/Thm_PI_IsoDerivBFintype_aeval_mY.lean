-- Prove2me | Theorems.Thm_PI_IsoDerivBFintype_aeval_mY
-- name    : PI.IsoDerivBFintype.aeval_mY
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:09:00.003406+00:00
-- url     : https://prove2.me/theorems/d7676f81-860e-5896-9599-50e3c876ee5d
-- title:
--   Iso Deriv BFintype: aeval m Y
-- statement:
--   The Iso Deriv BFintype construction uses the aeval m Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/IsoDerivB.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/IsoDerivB.lean#L59-L67

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
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) (nu : Lt → YoungDiagram)

theorem PI.IsoDerivBFintype.aeval_mY (J : ColChoice N nu) :
    MvPolynomial.aeval (gD s y') (mY tp nu J) =
      ∑ I : ColChoice N' nu, PIJ tp nu s I J * MvPolynomial.C (minY N' nu I (frC tp y')) := by sorry
