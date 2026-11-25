-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_lie_wL
-- name    : PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.lie_wL
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:42.8669+00:00
-- url     : https://prove2.me/theorems/e6ede31e-61d8-43ee-a0e2-9a16a8eab5a6
-- title:
--   Grothendieck Commutativity: lie w L
-- statement:
--   The Grothendieck Commutativity construction uses the lie w L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/RightRegularActionListDLREqAppend.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/RightRegularActionListDLREqAppend.lean#L77-L81

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

theorem PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.lie_wL {u : List (B.Mat k r)} (hu : ∀ X ∈ u, B.inLie k r X) : ∀ x ∈ wL u, B.inLie k r x.2 := by sorry
