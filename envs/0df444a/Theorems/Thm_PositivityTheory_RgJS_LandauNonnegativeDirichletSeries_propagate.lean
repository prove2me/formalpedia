-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_LandauNonnegativeDirichletSeries_propagate
-- name    : PositivityTheory.RgJS.LandauNonnegativeDirichletSeries.propagate
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:55.677802+00:00
-- url     : https://prove2.me/theorems/d4ef37ae-101f-4eb1-8b32-381e84f652a4
-- title:
--   Landau Nonnegative Dirichlet Series: propagate
-- statement:
--   The Landau Nonnegative Dirichlet Series construction uses the propagate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/LandauIteratedDerivatives/LandauL.lean#L77-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/LandauIteratedDerivatives/LandauL.lean#L77-L128

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

theorem PositivityTheory.RgJS.LandauNonnegativeDirichletSeries.propagate (f g : ℂ → ℂ) (a b : ℝ) (hf : ∀ σ : ℝ, a < σ → AnalyticAt ℂ f σ)
    (hg : ∀ σ : ℝ, a < σ → AnalyticAt ℂ g σ) (he : ∀ σ : ℝ, b < σ → f σ = g σ) :
    ∀ σ : ℝ, a < σ → f =ᶠ[𝓝 (σ : ℂ)] g := by sorry
