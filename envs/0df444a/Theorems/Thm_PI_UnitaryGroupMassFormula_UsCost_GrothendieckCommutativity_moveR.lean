-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_moveR
-- name    : PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.moveR
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:04:44.007497+00:00
-- url     : https://prove2.me/theorems/f4a53db6-5493-44a9-b4cc-e5c74356b446
-- title:
--   Grothendieck Commutativity: move R
-- statement:
--   The Grothendieck Commutativity construction uses the move R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/RightRegularActionListDLREqAppend.lean#L89-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/RightRegularActionListDLREqAppend.lean#L89-L102

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

theorem PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.moveR {X : B.Mat k r} (hX : B.inLie k r X) : ∀ (u : List (B.Mat k r)), (∀ Y ∈ u, B.inLie k r Y) →
    ∀ {h : B.Mat k r → E}, B.CkOn ((u.length + 1 : ℕ) : ℕ∞) (B.GV k r) h →
    ∀ g ∈ B.GV k r, Dx (false, X) (Dw (wL u) h) g = Dw (wL u) (Dx (false, X) h) g
  := by sorry
