-- Prove2me | Theorems.Thm_Section5BooleanFrame_tilted_centered_bilinear_mgf
-- name    : Section5BooleanFrame.tilted_centered_bilinear_mgf
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:05.998502+00:00
-- url     : https://prove2.me/theorems/0e20904f-5785-4f8b-bc7f-36610efdbf1a
-- title:
--   Centered scalar bilinear MGF under a tilted sign law
-- statement:
--   Let w,u,v∈R^I be unit vectors on finite I, and let s have probability 2^(−|I|)(Σ_iw_i s_i)². Put Y=(Σ_iu_i s_i)(Σ_iv_i s_i)−E[(Σ_iu_i s_i)(Σ_iv_i s_i)]. For every real λ with 512|λ|≤1/2, $$\mathbb E[e^{\lambda Y}]\le\exp(32\cdot512^2\lambda^2).$$ This is a scalar bilinear exponential-moment bound.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5TiltedBilinearMGF.lean, lines 56–60. Uses the fixed-scale Bernstein MGF argument by Nickrobbins95, Prove2Me theorem ffb81651-cac7-4739-85c2-9cb4b69885be, accepted submission 997bda66-5ba4-4af2-8457-558693e93561, copied in Solutions/Section5BernsteinFoundation.lean.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5FiniteProbabilityLaw
import Definitions.Def_Section5Verified_Section5TiltedFrameTail
import Definitions.Def_Section5Verified_Section5TiltedProjectionMGF
import Mathlib
import Theorems.Thm_Section5BernsteinFoundation_hdpc_subE_mgf
import Theorems.Thm_Section5BooleanFrame_amplitude_fourth
import Theorems.Thm_Section5BooleanFrame_tilted_amplitude_square_tail
import Theorems.Thm_Section5FiniteProbability_centered_exponential_of_raw
import Theorems.Thm_Section5FiniteProbability_exponential_midpoint
import Theorems.Thm_Section5FiniteProbability_exponential_moment_of_tail
import Theorems.Thm_Section5FiniteProbability_law_integral
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
open MeasureTheory ProbabilityTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (ι → Bool)] [MeasurableSingletonClass (ι → Bool)]

theorem Section5BooleanFrame.tilted_centered_bilinear_mgf (w u v : ι → ℝ) (hw : ∑ i, w i^2=1)
    (hu : ∑ i, u i^2=1) (hv : ∑ i, v i^2=1) (l : ℝ) (hl : |l| *512 ≤ 1/2) :
    mgf (fun x => Section5BooleanFrame.amplitude u x*Section5BooleanFrame.amplitude v x-
      (∫ y, Section5BooleanFrame.amplitude u y*Section5BooleanFrame.amplitude v y ∂Section5BooleanFrame.probabilityLaw w hw))
      (Section5BooleanFrame.probabilityLaw w hw) l ≤ Real.exp (32*l^2*512^2) := by sorry
