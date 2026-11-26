-- Prove2me | Theorems.Thm_Section5BooleanFrame_amplitude_fourth
-- name    : Section5BooleanFrame.amplitude_fourth
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:10:46.332027+00:00
-- url     : https://prove2.me/theorems/e28c05f3-8f04-5abb-9fb6-b578d7b34c2b
-- title:
--   Exact fourth moment of a Rademacher sum
-- statement:
--   Let $w$ be a real vector on a finite set and let $s_i$ be independent uniform signs. Then
--
--   $$\mathbb E\left(\sum_iw_i s_i\right)^4=3\left(\sum_iw_i^2\right)^2-2\sum_iw_i^4.$$
--
--   The identity supplies the fourth-moment control used for tilted sampling.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5BooleanFrameFourthMoment.lean, lines 10–38.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
import Theorems.Thm_Section5BooleanFrame_tilted_covariance
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Section5BooleanFrame.amplitude_fourth (w : ι → ℝ) :
    Section5BooleanFrame.average (fun x => Section5BooleanFrame.amplitude w x^4)=3*(∑ i, w i^2)^2-2*(∑ i, w i^4) := by sorry
