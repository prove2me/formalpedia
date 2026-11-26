-- Prove2me | Theorems.Thm_Section5BooleanFrame_tilted_amplitude_square_tail
-- name    : Section5BooleanFrame.tilted_amplitude_square_tail
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:54:38.639712+00:00
-- url     : https://prove2.me/theorems/bc30cc0b-f5a2-4006-a89a-ab40e7986f69
-- title:
--   Scalar projection-square tail under amplitude tilting
-- statement:
--   Let I be finite and w,u∈R^I satisfy Σ_iw_i²=Σ_iu_i²=1. Give a sign string s probability 2^(−|I|)(Σ_iw_i s_i)². For every t≥0 its scalar projection amplitude obeys $$\Pr[(\sum_i u_i s_i)^2\ge t]\le3e^{-t/4}.$$ This is a scalar tail estimate for the tilted sign law.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5TiltedFrameTail.lean, lines 48–51.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5TiltedFrameTail
import Mathlib
import Theorems.Thm_Section5BooleanFrame_amplitude_absolute_tail
import Theorems.Thm_Section5BooleanFrame_amplitude_fourth
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Section5BooleanFrame.tilted_amplitude_square_tail (w u : ι → ℝ) (hw : ∑ i, w i^2=1)
    (hu : ∑ i, u i^2=1) (t : ℝ) (ht : 0 ≤ t) :
    Section5BooleanFrame.tiltedMean w (fun x => if t ≤ Section5BooleanFrame.amplitude u x^2 then 1 else 0) ≤
      3*Real.exp (-t/4) := by sorry
