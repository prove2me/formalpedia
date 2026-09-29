-- Prove2me | Theorems.Thm_SchrodingerEquation_energy_quantization
-- name    : SchrodingerEquation.energy_quantization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T18:24:44.326452+00:00
-- url     : https://prove2.me/theorems/b246e07e-f783-4773-bc41-ff09b87f7fd6
-- title:
--   Energy quantization in the infinite well: $E = n^2\pi^2\hbar^2/(2mL^2)$
-- statement:
--   Let $\hbar > 0$, $m > 0$ and $L > 0$, and let $\psi : \mathbb{R} \to \mathbb{C}$ be a stationary state of energy $E$ for the one-dimensional infinite potential well of width $L$: $\psi$ is continuous on $[0, L]$, twice differentiable inside the box, satisfies
--   $$-\frac{\hbar^{2}}{2m}\psi''(x) = E\,\psi(x) \qquad (0 < x < L),$$
--   and obeys $\psi(0) = \psi(L) = 0$. Assume $\psi$ is not identically zero inside the box, i.e. $\psi(x) \neq 0$ for some $x \in (0, L)$.
--
--   Then the energy is quantized: there is a positive integer $n$ with
--   $$E = \frac{n^{2}\pi^{2}\hbar^{2}}{2 m L^{2}}.$$
--
--   This is the conclusion of the particle-in-a-box example: the boundary conditions at the walls admit non-trivial solutions only for this discrete set of energies. In particular the lowest admissible energy is $E_1 = \pi^2\hbar^2/(2mL^2) > 0$.
-- source:
--   Schrödinger equation, Wikipedia (revision retrieved 2026-09-21), https://en.wikipedia.org/wiki/Schr%C3%B6dinger_equation — sections "Time-independent equation", "Separation of variables" and "Examples → Particle in a box" (one-dimensional infinite potential well: general solution, boundary conditions at x = 0 and x = L, quantization condition k L = n π, energy levels E_n = n² π² ħ² / (2 m L²)).

import Definitions.Def_SchrodingerEquation_infinite_well_model

namespace SchrodingerEquation

theorem energy_quantization (hbar m L E : ℝ) (psi : ℝ → ℂ)
    (hbar_pos : 0 < hbar) (hm : 0 < m) (hL : 0 < L)
    (hpsi : IsStationaryState hbar m L E psi)
    (hne : ∃ x ∈ Set.Ioo 0 L, psi x ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ E = energyLevel hbar m L n := by sorry

end SchrodingerEquation
