-- Prove2me | Theorems.Thm_Section5BooleanFrame_diagonal_corrected_covariance
-- name    : Section5BooleanFrame.diagonal_corrected_covariance
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:10:59.024805+00:00
-- url     : https://prove2.me/theorems/bfd62b32-b671-48fa-b65c-9463c4cbce51
-- title:
--   Diagonal correction recovers a rank one covariance
-- statement:
--   For a real vector $w$ on a finite index set with $\sum_iw_i^2=1$, let $s$ be uniform independent signs and let $p_w(s)=2^{-|I|}(\sum_iw_i s_i)^2$. For every $i,j$,
--
--   $$\frac{\sum_s p_w(s)s_i s_j-\delta_{ij}}2+\delta_{ij}w_i^2=w_iw_j.$$
--
--   This identifies the diagonal correction needed to obtain the rank-one matrix $ww^T$.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5BooleanFrameCovariance.lean, lines 62–70.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
import Theorems.Thm_Section5BooleanFrame_tilted_covariance
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Section5BooleanFrame.diagonal_corrected_covariance (w : ι → ℝ) (hw : ∑ k, w k ^ 2=1) (i j : ι) :
    ((∑ x, Section5BooleanFrame.weight w x*(Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j))-(if i=j then 1 else 0))/2+
      (if i=j then w i ^ 2 else 0)=w i*w j := by sorry
