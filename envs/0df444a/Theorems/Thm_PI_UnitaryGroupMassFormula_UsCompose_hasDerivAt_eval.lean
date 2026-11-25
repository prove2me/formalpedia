-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_hasDerivAt_eval
-- name    : PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_eval
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:03:07.206805+00:00
-- url     : https://prove2.me/theorems/0b54f6de-31c9-4bcc-9c9f-6c0faf059545
-- title:
--   Us Compose: has Deriv At eval
-- statement:
--   The Us Compose construction uses the has Deriv At eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/HasDerivAtInvpow.lean#L13-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/HasDerivAtInvpow.lean#L13-L38

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

theorem PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_eval {σ : Type*} [Fintype σ] (v : ℝ → σ → ℂ) (v' : σ → ℂ)
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) 0) (q : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => eval (v t) q) (∑ i, eval (v 0) (pderiv i q) * v' i) 0 := by sorry
