-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Sieg_isClosed_image_section
-- name    : PositivityTheory.ThKR.Sieg.isClosed_image_section
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:06.668238+00:00
-- url     : https://prove2.me/theorems/6a8321a4-a768-47c8-8efd-4dc5ca40f8c0
-- title:
--   Sieg: is Closed image section
-- statement:
--   The Sieg construction uses the is Closed image section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L130-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L130-L133

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {r : ℕ}

theorem PositivityTheory.ThKR.Sieg.isClosed_image_section {X : Type} [TopologicalSpace X] [T2Space X] (τ : X → Fin r → ℝ) (hτ : Continuous τ)
    (a : (Fin r → ℝ) → X) (ha : Continuous a) (h : ∀ t, τ (a t) = t) {D : Set (Fin r → ℝ)} (hD : IsClosed D) :
    IsClosed (a '' D) := by sorry
