-- Prove2me | Theorems.Thm_Section5BooleanFrame_amplitude_mgf
-- name    : Section5BooleanFrame.amplitude_mgf
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:04:18.255715+00:00
-- url     : https://prove2.me/theorems/894abf84-775b-5d33-8169-c38d3c6ce581
-- title:
--   Exact moment generating function of a sign amplitude
-- statement:
--   For a real vector $u$ on a finite set $I$, independent uniform signs $s_i$, and any $t\in\mathbb R$, put $A_u=\sum_i u_i s_i$. Then
--
--   $$\mathbb E e^{tA_u}=\prod_{i\in I}\cosh(tu_i).$$
--
--   This is the exact exponential-moment identity for a Rademacher sum.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5BooleanFrameMGF.lean, lines 9–25.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Section5BooleanFrame.amplitude_mgf (u : ι → ℝ) (t : ℝ) :
    average (fun x => Real.exp (t*amplitude u x))=∏ i, Real.cosh (t*u i) := by sorry
