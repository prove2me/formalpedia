-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_LandauNonnegativeDirichletSeries_summable_pow
-- name    : PositivityTheory.RgJS.LandauNonnegativeDirichletSeries.summable_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:39.714238+00:00
-- url     : https://prove2.me/theorems/74b33066-19a3-5986-a2bd-bd12648cb045
-- title:
--   Landau Nonnegative Dirichlet Series: summable pow
-- statement:
--   The Landau Nonnegative Dirichlet Series construction uses the summable pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/LandauIteratedDerivatives/LandauL.lean#L10-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/LandauIteratedDerivatives/LandauL.lean#L10-L31

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

theorem PositivityTheory.RgJS.LandauNonnegativeDirichletSeries.summable_pow {ι : Type} (b μ : ι → ℝ) (hb : ∀ j, 0 ≤ b j) (hμ : ∀ j, 0 ≤ μ j) (a : ℝ)
    (h : ∀ σ : ℝ, a < σ → Summable (fun j => b j * Real.exp (-(μ j) * σ))) (n : ℕ) (σ : ℝ) (hσ : a < σ) :
    Summable (fun j => b j * μ j ^ n * Real.exp (-(μ j) * σ)) := by sorry
