-- Prove2me | Theorems.Thm_QMaxCutSDP_Rounding_final_min
-- name    : QMaxCutSDP.Rounding.final_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:11.200652+00:00
-- url     : https://prove2.me/theorems/9638653c-1b45-4fb2-a872-43052cd49707
-- title:
--   Proof of Theorem 1 — final numerical minimum is at least 0.562
-- statement:
--   With $\alpha_0=0.041$ and $\alpha_{\mathrm{GW}}$ the Goemans–Williamson constant, the scalar expression obtained in the final line of the proof satisfies, for every $\gamma\in[0,1]$,
--   $$0.562\le\frac{\alpha_{\mathrm{GW}}}{6}\left[1+2\sqrt{1-e^{-2\alpha_0\gamma}}e^{-\alpha_0(1-\gamma)}+e^{-2\alpha_0(1-\gamma)}\right]\frac{2+\gamma}{1+\gamma}.$$
--   This is the numerical step that yields the paper's claimed approximation factor from its edge-energy estimates.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, arXiv:2209.00789v1, p. 13, proof of Theorem 1, final minimum

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory

namespace QMaxCutSDP.Rounding

/-- Lee, proof of Theorem 1, p. 13: the last numerical minimum is at least 0.562. -/
theorem final_min (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    (0.562 : ℝ) ≤ alphaGW / 6 *
      (1 + 2 * Real.sqrt (1 - Real.exp (-2 * alpha0 * γ)) *
        Real.exp (-alpha0 * (1 - γ)) + Real.exp (-2 * alpha0 * (1 - γ))) *
      ((2 + γ) / (1 + γ)) := by sorry
end QMaxCutSDP.Rounding
