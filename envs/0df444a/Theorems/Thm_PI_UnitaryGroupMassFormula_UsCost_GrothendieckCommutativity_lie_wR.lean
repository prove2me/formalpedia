-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_lie_wR
-- name    : PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.lie_wR
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:51.807327+00:00
-- url     : https://prove2.me/theorems/a7ebec05-f0fb-41bf-b0ad-a0cdbda5c823
-- title:
--   Grothendieck Commutativity: lie w R
-- statement:
--   The Grothendieck Commutativity construction uses the lie w R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/RightRegularActionListDLREqAppend.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/RightRegularActionListDLREqAppend.lean#L83-L87

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

theorem PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.lie_wR {v : List (B.Mat k r)} (hv : ∀ X ∈ v, B.inLie k r X) : ∀ x ∈ wR v, B.inLie k r x.2 := by sorry
