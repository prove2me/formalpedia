-- Prove2me | Theorems.Thm_Section5BooleanFrame_tilted_centered_projection_mgf
-- name    : Section5BooleanFrame.tilted_centered_projection_mgf
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:22.969639+00:00
-- url     : https://prove2.me/theorems/67c2b69b-b3ca-5c56-b71a-496ce99d1b0c
-- title:
--   Centered scalar projection MGF under a tilted sign law
-- statement:
--   Let w,u∈R^I be unit vectors on finite I, and let s have probability 2^(−|I|)(Σ_iw_i s_i)². Put Y=(Σ_iu_i s_i)²−E[(Σ_iu_i s_i)²]. For every real λ with 512|λ|≤1/2, $$\mathbb E[e^{\lambda Y}]\le\exp(32\cdot512^2\lambda^2).$$ This controls one centered scalar projection.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5TiltedProjectionMGF.lean, lines 85–88. Uses the fixed-scale Bernstein MGF argument by Nickrobbins95, Prove2Me theorem ffb81651-cac7-4739-85c2-9cb4b69885be, accepted submission 997bda66-5ba4-4af2-8457-558693e93561, copied in Solutions/Section5BernsteinFoundation.lean.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5FiniteProbabilityLaw
import Definitions.Def_Section5Verified_Section5TiltedFrameTail
import Definitions.Def_Section5Verified_Section5TiltedProjectionMGF
import Mathlib
import Theorems.Thm_Section5BernsteinFoundation_hdpc_subE_mgf
import Theorems.Thm_Section5BooleanFrame_amplitude_fourth
import Theorems.Thm_Section5BooleanFrame_tilted_amplitude_square_tail
import Theorems.Thm_Section5FiniteProbability_exponential_moment_of_tail
import Theorems.Thm_Section5FiniteProbability_law_integral
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
open MeasureTheory ProbabilityTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (ι → Bool)] [MeasurableSingletonClass (ι → Bool)]

theorem Section5BooleanFrame.tilted_centered_projection_mgf (w u : ι → ℝ) (hw : ∑ i, w i^2=1)
    (hu : ∑ i, u i^2=1) (l : ℝ) (hl : |l| *512 ≤ 1/2) :
    mgf (fun x => Section5BooleanFrame.amplitude u x^2-(∫ y, Section5BooleanFrame.amplitude u y^2 ∂Section5BooleanFrame.probabilityLaw w hw))
      (Section5BooleanFrame.probabilityLaw w hw) l ≤ Real.exp (32*l^2*512^2) := by sorry
