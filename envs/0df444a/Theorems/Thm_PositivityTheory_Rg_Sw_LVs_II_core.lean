-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_core
-- name    : PositivityTheory.Rg.Sw.LVs.II.core
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:58.718292+00:00
-- url     : https://prove2.me/theorems/8a776493-2c2a-48cf-be3b-e5d33261b00f
-- title:
--   II: core
-- statement:
--   The II construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IILeft.lean#L81-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IILeft.lean#L81-L145

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.II.core {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n)
    (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hKU : KSet n ⊆ U) (hF : ContDiffOn ℝ 1 F U)
    (E : M2 n) (hE : Eᴴ = -E) (hEJ : E * JJ n = JJ n * E) :
    Integrable (fun k => fderiv ℝ F (ι k) (E * ι k)) μ ∧ ∫ k, fderiv ℝ F (ι k) (E * ι k) ∂μ = 0 := by sorry
