-- Prove2me | Theorems.Thm_SchrodingerEquation_quantized_wavenumber
-- name    : SchrodingerEquation.quantized_wavenumber
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T19:32:47.361057+00:00
-- url     : https://prove2.me/theorems/1676f63e-bcb6-4cfa-8370-ac6fd3ce4d20
-- title:
--   $\sin(kL) = 0$ with $k, L > 0$ forces $kL = n\pi$ for an integer $n \ge 1$
-- statement:
--   Let $k > 0$ and $L > 0$ be real numbers with $\sin(k L) = 0$. Then there is a positive integer $n$ such that
--   $$k L = n \pi.$$
--
--   This is the arithmetic half of the quantization argument: once the wall condition at $x = L$ has been reduced to $\sin(kL) = 0$, positivity of $k$ and $L$ turns the zero set of the sine into the positive integer multiples of $\pi$.
-- source:
--   Schrödinger equation, Wikipedia (revision retrieved 2026-09-21), https://en.wikipedia.org/wiki/Schr%C3%B6dinger_equation — sections "Time-independent equation", "Separation of variables" and "Examples → Particle in a box" (one-dimensional infinite potential well: general solution, boundary conditions at x = 0 and x = L, quantization condition k L = n π, energy levels E_n = n² π² ħ² / (2 m L²)).

import Definitions.Def_SchrodingerEquation_infinite_well_model

namespace SchrodingerEquation

theorem quantized_wavenumber (k L : ℝ) (hk : 0 < k) (hL : 0 < L)
    (h : Real.sin (k * L) = 0) :
    ∃ n : ℕ, 1 ≤ n ∧ k * L = (n : ℝ) * Real.pi := by sorry

end SchrodingerEquation
