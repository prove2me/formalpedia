-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_rightRegularAction_list_dLR_eq_append
-- name    : PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.rightRegularAction_list_dLR_eq_append
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:05:55.622821+00:00
-- url     : https://prove2.me/theorems/082c2569-ee5a-4aa1-8e75-21104ee0a388
-- title:
--   Grothendieck Commutativity: right Regular Action list d LR eq append
-- statement:
--   The Grothendieck Commutativity construction uses the right Regular Action list d LR eq append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/RightRegularActionListDLREqAppend.lean#L104-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/RightRegularActionListDLREqAppend.lean#L104-L126

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_RightRegularActionListDLREqAppend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
attribute [local instance] PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.clmNACG
attribute [local instance] PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.clmNS

theorem PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.rightRegularAction_list_dLR_eq_append {f : B.Mat k r → E} {m : ℕ} (hf : B.CkOn (m : ℕ∞) (B.GV k r) f) (u v : List (B.Mat k r))
    (hu : ∀ X ∈ u, B.inLie k r X) (hv : ∀ X ∈ v, B.inLie k r X) :
    ∀ w : List (B.Mat k r), (∀ X ∈ w, B.inLie k r X) → u.length + v.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, B.Rw w (B.dLR u v f) g = B.dLR u (w ++ v) f g
  := by sorry
