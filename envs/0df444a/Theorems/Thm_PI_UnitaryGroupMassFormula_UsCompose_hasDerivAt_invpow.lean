-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_hasDerivAt_invpow
-- name    : PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_invpow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:03:49.985905+00:00
-- url     : https://prove2.me/theorems/cf9bd9ac-cc16-4df0-865b-32c0882e0f99
-- title:
--   Us Compose: has Deriv At invpow
-- statement:
--   The Us Compose construction uses the has Deriv At invpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/HasDerivAtInvpow.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/HasDerivAtInvpow.lean#L78-L89

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

theorem PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_invpow {c : ℝ → ℂ} {c' : ℂ} (hc : HasDerivAt c c' 0) (h0 : c 0 ≠ 0) (a : ℕ) :
    HasDerivAt (fun t => (c t)⁻¹ ^ a) (-(a : ℂ) * c' * (c 0)⁻¹ ^ (a + 1)) 0 := by sorry
