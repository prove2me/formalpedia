-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_hasDerivAt_sv
-- name    : PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_sv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:42:39.513577+00:00
-- url     : https://prove2.me/theorems/d6f2b504-3e1d-4957-a2c5-6d9579803d47
-- title:
--   Us Compose: has Deriv At sv
-- statement:
--   The Us Compose construction uses the has Deriv At sv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/HasDerivAtInvpow.lean#L91-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/HasDerivAtInvpow.lean#L91-L111

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

theorem PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_sv {k j ρ : ℕ} (X g : Mat k (j + ρ)) (hg : DjU k j ρ g ≠ 0) (s : SC (2 * (j + ρ) + k + 1)) :
    HasDerivAt (fun t => sv k j ρ s (crv (false, X) g t))
      (sv k j ρ (dP X s.1, s.2.1, s.2.2) g
        + sv k j ρ (C (-(s.2.1 : ℂ)) * s.1 * dP X (qD k j ρ), s.2.1 + 1, s.2.2) g
        + sv k j ρ (C (-(s.2.2 : ℂ)) * s.1 * dP X (qDb k j ρ), s.2.1, s.2.2 + 1) g) 0 := by sorry
