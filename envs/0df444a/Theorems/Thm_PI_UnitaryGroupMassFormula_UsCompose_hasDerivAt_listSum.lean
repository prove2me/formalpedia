-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_hasDerivAt_listSum
-- name    : PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_listSum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:44:37.273797+00:00
-- url     : https://prove2.me/theorems/d1a91699-ea9f-5df7-91d8-309a488aa181
-- title:
--   Us Compose: has Deriv At list Sum
-- statement:
--   The Us Compose construction uses the has Deriv At list Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Expand.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Expand.lean#L63-L70

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

theorem PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_listSum {α : Type*} (L : List α) (f : α → ℝ → E) (f' : α → E)
    (h : ∀ a ∈ L, HasDerivAt (f a) (f' a) 0) :
    HasDerivAt (fun t => (L.map fun a => f a t).sum) (L.map f').sum 0 := by sorry
