-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Sieg_Heis_mul_def
-- name    : PositivityTheory.ThKR.Sieg.Heis.mul_def
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:16.271555+00:00
-- url     : https://prove2.me/theorems/8bcba647-0eb6-410a-98a8-196141418d10
-- title:
--   Heis: mul def
-- statement:
--   The Heis construction uses the mul def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L51-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L51-L51

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_SiegelHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Sieg
variable {A B : Type} [AddCommGroup A] [AddCommGroup B]
variable (β : A →+ A →+ B)

theorem PositivityTheory.ThKR.Sieg.Heis.mul_def (x y : Heis β) : x * y = (x.1 + y.1, x.2 + y.2 + β x.1 y.1) := by sorry
