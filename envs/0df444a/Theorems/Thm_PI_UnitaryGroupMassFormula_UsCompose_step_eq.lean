-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_step_eq
-- name    : PI.UnitaryGroupMassFormula.UsCompose.step_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:52:20.294809+00:00
-- url     : https://prove2.me/theorems/7914bb53-ba28-494c-9dee-4683acab79a2
-- title:
--   Us Compose: step eq
-- statement:
--   The Us Compose construction uses the step eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Expand.lean#L84-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Expand.lean#L84-L114

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PI.UnitaryGroupMassFormula.UsCompose.step_eq {k j ρ m : ℕ} {F : Mat k (j + ρ) → E} (hF : CkOn (m : ℕ∞) (GV k (j + ρ)) F)
    {X : Mat k (j + ρ)} (hX : inLie k (j + ρ) X) {L : FS k (j + ρ)}
    (hL : ∀ e ∈ L, ∀ Y ∈ e.2, inLie k (j + ρ) Y) (hm : ∀ e ∈ L, e.2.length + 1 ≤ m)
    {g : Mat k (j + ρ)} (hg : g ∈ GV k (j + ρ)) (hD : DjU k j ρ g ≠ 0) :
    RdV X (shape k j ρ F L) g = shape k j ρ F (step k j ρ X L) g := by sorry
