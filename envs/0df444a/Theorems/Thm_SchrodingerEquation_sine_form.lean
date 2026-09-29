-- Prove2me | Theorems.Thm_SchrodingerEquation_sine_form
-- name    : SchrodingerEquation.sine_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T18:49:26.042989+00:00
-- url     : https://prove2.me/theorems/2bd2ea2d-3eed-4d84-9a07-cf41236f95ee
-- title:
--   Positive-energy stationary states are $C\sin(kx)$ with $k=\sqrt{2mE}/\hbar$
-- statement:
--   Let $\hbar > 0$, $m > 0$, $L > 0$ and $E > 0$, and set the wave number
--   $$k = \frac{\sqrt{2 m E}}{\hbar}.$$
--   If $\psi : \mathbb{R} \to \mathbb{C}$ is a stationary state of energy $E$ for the infinite well of width $L$, then there is a complex constant $C$ with
--   $$\psi(x) = C \sin(k x) \qquad \text{for all } x \in [0, L].$$
--
--   This is the content of the textbook step that writes the general solution as $A e^{ikx} + B e^{-ikx}$ and then uses $\psi(0) = 0$ to eliminate the cosine part, leaving a multiple of $\sin(kx)$. The constant $C$ is not determined here: it is fixed only up to normalization and phase.
-- source:
--   Schrödinger equation, Wikipedia (revision retrieved 2026-09-21), https://en.wikipedia.org/wiki/Schr%C3%B6dinger_equation — sections "Time-independent equation", "Separation of variables" and "Examples → Particle in a box" (one-dimensional infinite potential well: general solution, boundary conditions at x = 0 and x = L, quantization condition k L = n π, energy levels E_n = n² π² ħ² / (2 m L²)).

import Definitions.Def_SchrodingerEquation_infinite_well_model

namespace SchrodingerEquation

theorem sine_form (hbar m L E : ℝ) (psi : ℝ → ℂ)
    (hbar_pos : 0 < hbar) (hm : 0 < m) (hL : 0 < L) (hE : 0 < E)
    (hpsi : IsStationaryState hbar m L E psi) :
    ∃ C : ℂ, ∀ x ∈ Set.Icc 0 L,
      psi x = C * (Real.sin (Real.sqrt (2 * m * E) / hbar * x) : ℂ) := by sorry

end SchrodingerEquation
