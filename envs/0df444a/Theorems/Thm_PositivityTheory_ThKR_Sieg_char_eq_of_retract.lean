-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Sieg_char_eq_of_retract
-- name    : PositivityTheory.ThKR.Sieg.char_eq_of_retract
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:30.974323+00:00
-- url     : https://prove2.me/theorems/0428bf17-3d44-4323-8709-7700806294ce
-- title:
--   Sieg: char eq of retract
-- statement:
--   The Sieg construction uses the char eq of retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L22-L25

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
variable {H N : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
  [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N]

theorem PositivityTheory.ThKR.Sieg.char_eq_of_retract (ι : N →* H) (hι : Continuous ι) (π : H → N) (hπ : Continuous π)
    (hmul : ∀ x p, π (ι x * p) = x * π p) (φ : H ≃ₜ* H) (ψ : N ≃ₜ* N) (h1 : ∀ p, π (φ p) = ψ (π p))
    (h2 : ∀ p, (ι (π (φ p)))⁻¹ * φ p = (ι (π p))⁻¹ * p) : mulEquivHaarChar φ = mulEquivHaarChar ψ := by sorry
