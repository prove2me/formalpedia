-- Prove2me | Theorems.Thm_SDDiP_Envelope_conv_binary_eq_cube
-- name    : SDDiP.Envelope.conv_binary_eq_cube
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:44:49.532726+00:00
-- url     : https://prove2.me/theorems/6e4ee295-961c-4fbc-a425-8bb968df81be
-- title:
--   Proof of Theorem 1, p. 496 — $\operatorname{conv}(\{0,1\}^n) = [0,1]^n$
-- statement:
--   For every $n \ge 0$, the convex hull of the binary points of $\mathbb R^n$ is the unit cube:
--   $$\operatorname{conv}\big(\{0,1\}^n\big) = C_n = [0,1]^n.$$
--
--   In the proof of Theorem 1 this identifies the domain $\operatorname{conv}(X)$ of Definition 3 with the cube and makes the dual program $(D)$ feasible at every $x \in [0,1]^n$.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 496, proof of Theorem 1 ('Since C_n is the convex hull of {0, 1}^n')

import Mathlib
import Definitions.Def_SDDiP_Envelope_ConvexLowerEnvelope

namespace SDDiP.Envelope

/-- Proof of Theorem 1, p. 496 (Zou, Ahmed, Sun, Math. Program. 175 (2019)): "`Cₙ` is the convex hull
of `{0,1}ⁿ`", i.e. `conv({0,1}ⁿ) = [0,1]ⁿ`. -/
theorem conv_binary_eq_cube (n : ℕ) : convexHull ℝ (binaryPoints n) = cube n := by sorry

end SDDiP.Envelope
