-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_LandauNonnegativeDirichletSeries_linL
-- name    : PositivityTheory.RgJS.LandauNonnegativeDirichletSeries.linL
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:56.865433+00:00
-- url     : https://prove2.me/theorems/705feac7-8b4d-4fce-a25e-1f87b897b923
-- title:
--   Landau Nonnegative Dirichlet Series: lin L
-- statement:
--   The Landau Nonnegative Dirichlet Series construction uses the lin L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/LandauIteratedDerivatives/LandauL.lean#L132-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/LandauIteratedDerivatives/LandauL.lean#L132-L240

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_LandauIteratedDerivatives_LandauL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.LandauNonnegativeDirichletSeries

theorem PositivityTheory.RgJS.LandauNonnegativeDirichletSeries.linL (I : Type) (c l : I → ℝ) (σ₀ σ₁ : ℝ) (F : ℂ → ℂ) (hc : ∀ i, 0 ≤ c i) (hl : ∀ i, 0 ≤ l i)
    (hF : ∀ σ : ℝ, σ₀ < σ → AnalyticAt ℂ F σ)
    (hS : ∀ σ : ℝ, σ₁ < σ → Summable fun i => c i * Real.exp (-(l i * σ)))
    (hE : ∀ σ : ℝ, σ₁ < σ → F σ = ∑' i, ((c i * Real.exp (-(l i * σ)) : ℝ) : ℂ)) :
    ∀ σ : ℝ, σ₀ < σ → Summable fun i => c i * Real.exp (-(l i * σ)) := by sorry
