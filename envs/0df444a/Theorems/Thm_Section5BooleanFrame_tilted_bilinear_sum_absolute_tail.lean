-- Prove2me | Theorems.Thm_Section5BooleanFrame_tilted_bilinear_sum_absolute_tail
-- name    : Section5BooleanFrame.tilted_bilinear_sum_absolute_tail
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:08:58.452443+00:00
-- url     : https://prove2.me/theorems/ed0d1d12-2edf-41ea-8977-f211df82618d
-- title:
--   Scalar concentration for a batch of tilted bilinear samples
-- statement:
--   Let I,J be finite, N=|J|, and let w,u,v∈R^I be unit. For independent sign strings s_r with amplitude-tilted law p_w(s)=2^(−|I|)(Σ_iw_i s_i)², put Y_r=(Σ_iu_i s_ri)(Σ_iv_i s_ri)−E[(Σ_iu_i s_i)(Σ_iv_i s_i)]. For every t≥0, $$\Pr[|\sum_{r\in J}Y_r|\ge Nt]\le2\exp\!\left(-N\min(t^2,t)/33554432\right).$$ The bound concerns a fixed scalar bilinear form.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5TiltedBatchConcentration.lean, lines 10–16. Uses the fixed-scale Bernstein MGF argument by Nickrobbins95, Prove2Me theorem ffb81651-cac7-4739-85c2-9cb4b69885be, accepted submission 997bda66-5ba4-4af2-8457-558693e93561, copied in Solutions/Section5BernsteinFoundation.lean.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5TiltedFrameTail
import Definitions.Def_Section5Verified_Section5TiltedProjectionMGF
import Mathlib
import Theorems.Thm_Section5BooleanFrame_tilted_centered_bilinear_mgf
import Theorems.Thm_Section5FiniteProbability_iid_subexponential_absolute_tail
import Theorems.Thm_Section5FiniteProbability_law_integral
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

theorem Section5BooleanFrame.tilted_bilinear_sum_absolute_tail (w u v : ι → ℝ) (hw : ∑ i, w i^2=1)
    (hu : ∑ i, u i^2=1) (hv : ∑ i, v i^2=1) (t : ℝ) (ht : 0 ≤ t) :
    (∑ x : J → ι → Bool, if (Fintype.card J : ℝ)*t ≤
      |∑ r, (Section5BooleanFrame.amplitude u (x r)*Section5BooleanFrame.amplitude v (x r)-
        Section5BooleanFrame.tiltedMean w (fun y => Section5BooleanFrame.amplitude u y*Section5BooleanFrame.amplitude v y))| then
          ∏ r, Section5BooleanFrame.weight w (x r) else 0) ≤
      2*Real.exp (-(Fintype.card J : ℝ)*min (t^2) t/33554432) := by sorry
