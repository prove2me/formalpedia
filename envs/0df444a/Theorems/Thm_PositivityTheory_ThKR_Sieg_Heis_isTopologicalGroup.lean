-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Sieg_Heis_isTopologicalGroup
-- name    : PositivityTheory.ThKR.Sieg.Heis.isTopologicalGroup
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:33.606933+00:00
-- url     : https://prove2.me/theorems/7676d11e-4682-41a8-82fc-f7d2f589c4f8
-- title:
--   Heis: is Topological Group
-- statement:
--   The Heis construction uses the is Topological Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L75-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L75-L82

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
variable [TopologicalSpace A] [TopologicalSpace B]
variable [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]

theorem PositivityTheory.ThKR.Sieg.Heis.isTopologicalGroup (hβ : Continuous fun p : A × A => β p.1 p.2) : IsTopologicalGroup (Heis β) := by sorry
