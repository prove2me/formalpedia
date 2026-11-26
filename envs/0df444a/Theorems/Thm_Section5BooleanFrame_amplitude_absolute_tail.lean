-- Prove2me | Theorems.Thm_Section5BooleanFrame_amplitude_absolute_tail
-- name    : Section5BooleanFrame.amplitude_absolute_tail
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:51:12.801128+00:00
-- url     : https://prove2.me/theorems/949135a8-d114-568c-b01b-bdd1c7fc25fb
-- title:
--   Two sided tail for a unit sign amplitude
-- statement:
--   For a real vector $u$ on a finite set with $\sum_i u_i^2=1$, independent uniform signs $s_i$, and $r\ge0$,
--
--   $$\Pr\!\left(\left|\sum_i u_i s_i\right|\ge r\right)\le2e^{-r^2/2}.$$
--
--   This is a uniform two-sided subgaussian tail bound.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5BooleanFrameTail.lean, lines 26–39.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
import Theorems.Thm_Section5BooleanFrame_amplitude_mgf_le
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Section5BooleanFrame.amplitude_absolute_tail (u : ι → ℝ) (hu : ∑ i, u i^2=1) (r : ℝ) (hr : 0 ≤ r) :
    Section5BooleanFrame.average (fun x => if r ≤ |Section5BooleanFrame.amplitude u x| then 1 else 0) ≤ 2*Real.exp (-r^2/2) := by sorry
