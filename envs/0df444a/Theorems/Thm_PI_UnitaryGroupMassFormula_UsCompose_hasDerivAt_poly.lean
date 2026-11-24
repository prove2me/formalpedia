-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_hasDerivAt_poly
-- name    : PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_poly
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:24:38.445074+00:00
-- url     : https://prove2.me/theorems/0a711305-a168-400a-8b6d-2e9720366f28
-- title:
--   Us Compose: has Deriv At poly
-- statement:
--   The Us Compose construction uses the has Deriv At poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/HasDerivAtInvpow.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/HasDerivAtInvpow.lean#L56-L63

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

theorem PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_poly {k r : ℕ} (X g : Mat k r) (q : MvPolynomial (Vr (2 * r + k + 1)) ℂ) :
    HasDerivAt (fun t => eval (vars (crv (false, X) g t)) q) (eval (vars g) (dP X q)) 0 := by sorry
