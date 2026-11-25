-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_crv_var
-- name    : PI.UnitaryGroupMassFormula.UsCompose.crv_var
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:05:56.210295+00:00
-- url     : https://prove2.me/theorems/66ca41b9-edd4-5d4b-99ea-c2bad629455c
-- title:
--   Us Compose: crv var
-- statement:
--   The Us Compose construction uses the crv var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/HasDerivAtInvpow.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/HasDerivAtInvpow.lean#L40-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PI.UnitaryGroupMassFormula.UsCompose.crv_var {k r : ℕ} (X g : Mat k r) (i : Vr (2 * r + k + 1)) :
    HasDerivAt (fun t => vars (crv (false, X) g t) i) (eval (vars g) (lin X i)) 0 := by sorry
