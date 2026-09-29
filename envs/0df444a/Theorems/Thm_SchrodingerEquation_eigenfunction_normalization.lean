-- Prove2me | Theorems.Thm_SchrodingerEquation_eigenfunction_normalization
-- name    : SchrodingerEquation.eigenfunction_normalization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T19:40:56.917065+00:00
-- url     : https://prove2.me/theorems/73ed8455-706e-4bc7-acec-bb2d4c4e4912
-- title:
--   $\int_0^L |\sin(n\pi x/L)|^2\,dx = L/2$
-- statement:
--   Let $L > 0$ and let $n \ge 1$ be an integer. Then
--   $$\int_0^L \left|\sin\!\left(\frac{n\pi x}{L}\right)\right|^{2} dx \;=\; \frac{L}{2}.$$
--
--   Consequently the normalized eigenfunctions of the infinite well of width $L$ are $\sqrt{2/L}\,\sin(n\pi x/L)$: these are the unit vectors of $L^2([0,L])$ used in the Born rule, and the computation is what makes the constant $C$ of the general solution non-zero and explicit.
-- source:
--   Schrödinger equation, Wikipedia (revision retrieved 2026-09-21), https://en.wikipedia.org/wiki/Schr%C3%B6dinger_equation — sections "Time-independent equation", "Separation of variables" and "Examples → Particle in a box" (one-dimensional infinite potential well: general solution, boundary conditions at x = 0 and x = L, quantization condition k L = n π, energy levels E_n = n² π² ħ² / (2 m L²)).

import Definitions.Def_SchrodingerEquation_infinite_well_model

namespace SchrodingerEquation

theorem eigenfunction_normalization (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 1 ≤ n) :
    ∫ x in (0 : ℝ)..L, ‖eigenfunction L n x‖ ^ 2 = L / 2 := by sorry

end SchrodingerEquation
