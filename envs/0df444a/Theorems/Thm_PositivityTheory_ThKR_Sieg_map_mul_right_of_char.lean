-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Sieg_map_mul_right_of_char
-- name    : PositivityTheory.ThKR.Sieg.map_mul_right_of_char
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:49.216153+00:00
-- url     : https://prove2.me/theorems/54d69a6f-1425-4265-925c-a6bc6a415f68
-- title:
--   Sieg: map mul right of char
-- statement:
--   The Sieg construction uses the map mul right of char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L208-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L208-L214

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

theorem PositivityTheory.ThKR.Sieg.map_mul_right_of_char (ν : Measure G) [ν.IsHaarMeasure] (b : G) (φ : G ≃ₜ* G) (hφ : ∀ p, φ p = b⁻¹ * p * b) :
    ν.map (· * b) = ((mulEquivHaarChar φ)⁻¹ : ℝ≥0) • ν := by sorry
