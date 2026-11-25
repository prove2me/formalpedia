-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_mem_steps
-- name    : PI.UnitaryGroupMassFormula.UsCompose.mem_steps
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:03:46.451892+00:00
-- url     : https://prove2.me/theorems/ab128def-8e90-4b2c-8133-fb5cc55561d1
-- title:
--   Us Compose: mem steps
-- statement:
--   The Us Compose construction uses the mem steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Expand.lean#L34-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Expand.lean#L34-L57

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

theorem PI.UnitaryGroupMassFormula.UsCompose.mem_steps {k j ρ : ℕ} {w : List (Mat k (j + ρ))} {L : FS k (j + ρ)} :
    ∀ {e : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ))}, e ∈ steps k j ρ w L →
    ∃ e₀ ∈ L, e.2.length ≤ e₀.2.length + w.length ∧ ∀ Y ∈ e.2, Y ∈ e₀.2 ∨ Y ∈ w := by sorry
