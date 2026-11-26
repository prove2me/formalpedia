-- Prove2me | Theorems.Thm_Section5BooleanFrame_tilted_covariance
-- name    : Section5BooleanFrame.tilted_covariance
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:09:18.395016+00:00
-- url     : https://prove2.me/theorems/79377cde-cb40-59b4-ad49-b7feb9491c95
-- title:
--   Amplitude weighted sign covariance
-- statement:
--   Let $I$ be finite, let $s$ be uniform independent signs, and put $A_w(s)=\sum_iw_i s_i$ for a real vector $w$. Then for every $i,j$,
--
--   $$\mathbb E[A_w(s)^2s_i s_j]=\delta_{ij}\sum_kw_k^2+2w_iw_j-2\delta_{ij}w_i^2.$$
--
--   This computes the covariance created by squared-amplitude weighting without assuming $w$ is normalized.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5BooleanFrameCovariance.lean, lines 29–51.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
import Theorems.Thm_Section5BooleanFrame_sign_fourth
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Section5BooleanFrame.tilted_covariance (w : ι → ℝ) (i j : ι) :
    Section5BooleanFrame.average (fun x => Section5BooleanFrame.amplitude w x ^ 2*(Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j))=
      (if i=j then ∑ k, w k ^ 2 else 0)+2*w i*w j-
        (if i=j then 2*w i ^ 2 else 0) := by sorry
