-- Prove2me | Theorems.Thm_Section5BooleanFrame_amplitude_mgf_le
-- name    : Section5BooleanFrame.amplitude_mgf_le
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:09:32.603464+00:00
-- url     : https://prove2.me/theorems/c55ccffd-6f70-5061-add7-93998587f8fa
-- title:
--   Subgaussian exponential moment for a sign amplitude
-- statement:
--   For a real vector $u$ on a finite set, independent uniform signs $s_i$, and $t\in\mathbb R$,
--
--   $$\mathbb E\exp\!\left(t\sum_i u_i s_i\right)\le\exp\!\left(\frac{t^2}2\sum_i u_i^2\right).$$
--
--   This controls the amplitude with its squared Euclidean norm as variance proxy.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5BooleanFrameMGF.lean, lines 27–41.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
import Theorems.Thm_Section5BooleanFrame_amplitude_mgf
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Section5BooleanFrame.amplitude_mgf_le (u : ι → ℝ) (t : ℝ) :
    Section5BooleanFrame.average (fun x => Real.exp (t*Section5BooleanFrame.amplitude u x)) ≤
      Real.exp (t^2*(∑ i, u i^2)/2) := by sorry
