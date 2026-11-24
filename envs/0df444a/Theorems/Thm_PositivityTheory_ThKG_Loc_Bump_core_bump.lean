-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_core_bump
-- name    : PositivityTheory.ThKG.Loc.Bump.core_bump
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:41.271638+00:00
-- url     : https://prove2.me/theorems/e305c576-9b99-415b-a5c4-b76267d7a1f7
-- title:
--   Bump: core bump
-- statement:
--   The Bump construction uses the core bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ExistsDensity.lean#L12-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ExistsDensity.lean#L12-L63

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace
variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

theorem PositivityTheory.ThKG.Loc.Bump.core_bump {Ω : Type} [TopologicalSpace Ω] [T2Space Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (π : Ω → X) (hπ : Continuous π) (x₀ : X) (G : Ω → ℂ) (U S : Set Ω)
    (hU : IsOpen U) (hG : ContinuousOn G U) (hS : IsCompact S) (hSU : S ⊆ U) (ε : ℝ) (hε : 0 < ε)
    (hb : ∀ p, dist (π p) x₀ ≤ ε → p ∈ S) (hpos : ∀ p, π p = x₀ → 0 < (G p).re) (p₀ : Ω) (h₀ : π p₀ = x₀) :
    ∃ φ : 𝓢(X, ℂ), (∀ p, φ (π p) ≠ 0 → p ∈ S) ∧ Integrable (fun p => φ (π p) * G p) μ ∧ ∫ p, φ (π p) * G p ∂μ ≠ 0 := by sorry
