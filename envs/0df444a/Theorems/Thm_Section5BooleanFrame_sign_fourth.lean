-- Prove2me | Theorems.Thm_Section5BooleanFrame_sign_fourth
-- name    : Section5BooleanFrame.sign_fourth
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:07:49.887298+00:00
-- url     : https://prove2.me/theorems/b52b5d83-d34e-5a77-90a3-f71856dcf580
-- title:
--   Fourth moment of independent Boolean signs
-- statement:
--   Let $I$ be finite, let $X$ be uniform on $\{0,1\}^I$, and put $s_i=(-1)^{X_i}$ and $\delta_{ij}=1$ if $i=j$ and $0$ otherwise. For all $i,j,k,l\in I$,
--
--   $$\mathbb E[s_i s_j s_k s_l]=\delta_{ij}\delta_{kl}+\delta_{ik}\delta_{jl}+\delta_{il}\delta_{jk}-2\delta_{ij}\delta_{ik}\delta_{il}.$$
--
--   This is the exact fourth-order sign identity, including coincident indices.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5BooleanFrameMoments.lean, lines 81–112.

import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Section5BooleanFrame.sign_fourth (i j k l : ι) :
    Section5BooleanFrame.average (fun x : ι → Bool => Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j*Section5BooleanFrame.sign x k*Section5BooleanFrame.sign x l)=
      (if i=j then 1 else 0)*(if k=l then 1 else 0)+
      (if i=k then 1 else 0)*(if j=l then 1 else 0)+
      (if i=l then 1 else 0)*(if j=k then 1 else 0)-
      2*(if i=j then 1 else 0)*(if i=k then 1 else 0)*(if i=l then 1 else 0) := by sorry
