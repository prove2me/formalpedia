-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_mem_step
-- name    : PI.UnitaryGroupMassFormula.UsCompose.mem_step
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:45:51.504512+00:00
-- url     : https://prove2.me/theorems/d88d9132-39c5-5203-97a4-38d7fd7f9dfd
-- title:
--   Us Compose: mem step
-- statement:
--   The Us Compose construction uses the mem step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Expand.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Expand.lean#L25-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
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

theorem PI.UnitaryGroupMassFormula.UsCompose.mem_step {k j ρ : ℕ} {X : Mat k (j + ρ)} {L : FS k (j + ρ)}
    {e : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ))} (he : e ∈ step k j ρ X L) :
    ∃ e₀ ∈ L, e.2 = e₀.2 ∨ e.2 = X :: e₀.2 := by sorry
