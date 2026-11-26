-- Prove2me | Theorems.Thm_Section5BooleanFrame_centeredCovariance_bilinear
-- name    : Section5BooleanFrame.centeredCovariance_bilinear
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:51:09.000434+00:00
-- url     : https://prove2.me/theorems/e735f707-2537-5888-b87c-f777f08526c3
-- title:
--   Bilinear empirical covariance as a centered scalar average
-- statement:
--   Let I,J be finite with N=|J|>0, let w,u,v∈R^I be arbitrary, and let s_r be specified sign strings. Write a_w(s)=2^(−|I|)(Σ_iw_i s_i)², S_w=Σ_sa_w(s)ss^T and C=N^(−1)Σ_rs_rs_r^T−S_w. Then $$u^TCv=N^{-1}\sum_r\left((u^Ts_r)(v^Ts_r)-\sum_sa_w(s)(u^Ts)(v^Ts)\right).$$ No normalization of w,u,v or randomness of the chosen samples is assumed.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5SampleCovarianceBilinear.lean, lines 45–50.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5CovarianceTracePolynomial
import Definitions.Def_Section5Verified_Section5SampleCovarianceBilinear
import Definitions.Def_Section5Verified_Section5TiltedFrameTail
import Mathlib
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

theorem Section5BooleanFrame.centeredCovariance_bilinear (hJ : Fintype.card J ≠ 0)
    (w u v : ι → ℝ) (x : J → ι → Bool) :
    Section5BooleanFrame.bilinear (Section5SignMoments.centeredCovariance (Section5BooleanFrame.populationCovariance w)
      (fun r => Section5BooleanFrame.sign (x r))) u v=
      (Fintype.card J : ℝ)⁻¹*(∑ r, (Section5BooleanFrame.amplitude u (x r)*Section5BooleanFrame.amplitude v (x r)-
        Section5BooleanFrame.tiltedMean w (fun y => Section5BooleanFrame.amplitude u y*Section5BooleanFrame.amplitude v y))) := by sorry
