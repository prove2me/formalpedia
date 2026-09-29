-- Prove2me | Theorems.Thm_SchrodingerEquation_trivial_of_energy_nonpos
-- name    : SchrodingerEquation.trivial_of_energy_nonpos
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T18:38:06.351515+00:00
-- url     : https://prove2.me/theorems/2ab9aebe-4eb2-486a-a16c-ddf9ca273738
-- title:
--   No bound state with $E \le 0$ in the infinite well
-- statement:
--   Let $\hbar > 0$, $m > 0$, $L > 0$ and let $E \le 0$. If $\psi : \mathbb{R} \to \mathbb{C}$ is a stationary state of energy $E$ for the infinite well of width $L$ — continuous on $[0,L]$, twice differentiable on $(0,L)$, solving $-\frac{\hbar^2}{2m}\psi'' = E\psi$ there, and vanishing at both walls — then $\psi$ vanishes identically on $[0, L]$.
--
--   This is the step of the textbook derivation that rules out non-positive energies before the trigonometric solutions are introduced: for $E < 0$ the general solution is a combination of $e^{\kappa x}$ and $e^{-\kappa x}$, and for $E = 0$ it is affine; in both cases two zeros force the solution to be trivial.
-- source:
--   Schrödinger equation, Wikipedia (revision retrieved 2026-09-21), https://en.wikipedia.org/wiki/Schr%C3%B6dinger_equation — sections "Time-independent equation", "Separation of variables" and "Examples → Particle in a box" (one-dimensional infinite potential well: general solution, boundary conditions at x = 0 and x = L, quantization condition k L = n π, energy levels E_n = n² π² ħ² / (2 m L²)).

import Definitions.Def_SchrodingerEquation_infinite_well_model

namespace SchrodingerEquation

theorem trivial_of_energy_nonpos (hbar m L E : ℝ) (psi : ℝ → ℂ)
    (hbar_pos : 0 < hbar) (hm : 0 < m) (hL : 0 < L) (hE : E ≤ 0)
    (hpsi : IsStationaryState hbar m L E psi) :
    ∀ x ∈ Set.Icc 0 L, psi x = 0 := by sorry

end SchrodingerEquation
