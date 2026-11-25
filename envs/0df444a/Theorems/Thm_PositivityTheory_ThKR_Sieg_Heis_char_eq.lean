-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Sieg_Heis_char_eq
-- name    : PositivityTheory.ThKR.Sieg.Heis.char_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:02:01.253353+00:00
-- url     : https://prove2.me/theorems/6da94982-09b3-42b9-bd77-e18623518d3c
-- title:
--   Heis: char eq
-- statement:
--   The Heis construction uses the char eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L87-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L87-L121

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
variable [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
  [LocallyCompactSpace B] [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B]

theorem PositivityTheory.ThKR.Sieg.Heis.char_eq [IsTopologicalGroup (Heis β)] (hβ : Continuous fun p : A × A => β p.1 p.2) (ψ : Heis β ≃ₜ* Heis β)
    (θ₁ : A ≃ₜ+ A) (θ₂ : B ≃ₜ+ B) (h : ∀ x, ψ x = (θ₁ x.1, θ₂ x.2)) :
    mulEquivHaarChar ψ = addEquivAddHaarChar θ₁ * addEquivAddHaarChar θ₂ := by sorry
