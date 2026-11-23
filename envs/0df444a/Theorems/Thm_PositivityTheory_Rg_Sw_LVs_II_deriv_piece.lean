-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_deriv_piece
-- name    : PositivityTheory.Rg.Sw.LVs.II.deriv_piece
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:55.574788+00:00
-- url     : https://prove2.me/theorems/a422503c-a0c9-46d8-b09b-93cf10806a08
-- title:
--   II: deriv piece
-- statement:
--   The II construction uses the deriv piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean#L23-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean#L23-L39

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame
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
open scoped ContDiff ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.II.deriv_piece (Θ : M2 n → ℂ) (x : M2 n) (hΘ : DifferentiableAt ℂ Θ x)
    (γ : ℝ → M2 n) (Y : M2 n) (hγ : HasDerivAt γ Y 0) (hγ0 : γ 0 = 1)
    (f : ℝ → ℂ) (r : ℂ) (hf : HasDerivAt f r 0)
    (hlaw : ∀ᶠ t in 𝓝 (0 : ℝ), Θ (γ t * x) = f t * Θ x) :
    fderiv ℂ Θ x (Y * x) = r * Θ x := by sorry
