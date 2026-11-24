-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_fourier_vanish
-- name    : PositivityTheory.ThKG.Loc.Bump.fourier_vanish
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:42.34519+00:00
-- url     : https://prove2.me/theorems/ad5c344f-818d-4ed1-904d-37ffc7c0f4b7
-- title:
--   Bump: fourier vanish
-- statement:
--   The Bump construction uses the fourier vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ExistsDensity.lean#L88-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ExistsDensity.lean#L88-L104

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
variable [MeasurableSpace X] [BorelSpace X]

theorem PositivityTheory.ThKG.Loc.Bump.fourier_vanish {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] (π : Ω → X) (hπ : Measurable π) (g : Ω → ℂ)
    (hg : Integrable g μ) (h : ∀ η, ∫ p, ch ⟪η, π p⟫ * g p ∂μ = 0) (φ : 𝓢(X, ℂ)) : ∫ p, φ (π p) * g p ∂μ = 0 := by sorry
