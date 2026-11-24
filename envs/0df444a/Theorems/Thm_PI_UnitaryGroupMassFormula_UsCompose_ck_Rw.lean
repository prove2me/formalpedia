-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_ck_Rw
-- name    : PI.UnitaryGroupMassFormula.UsCompose.ck_Rw
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:50:18.285169+00:00
-- url     : https://prove2.me/theorems/91eef8b5-0af2-41ab-ac30-2f928b53fe18
-- title:
--   Us Compose: ck Rw
-- statement:
--   The Us Compose construction uses the ck Rw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Expand.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Expand.lean#L77-L82

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

theorem PI.UnitaryGroupMassFormula.UsCompose.ck_Rw {k r m : ℕ} {F : Mat k r → E} (hF : CkOn (m : ℕ∞) (GV k r) F) {v : List (Mat k r)}
    (hv : ∀ X ∈ v, inLie k r X) (n : ℕ) (hn : n + v.length ≤ m) : CkOn (n : ℕ∞) (GV k r) (Rw v F) := by sorry
