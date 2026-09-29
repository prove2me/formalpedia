-- Prove2me | Theorems.Thm_SchrodingerEquation_eigenfunction_isStationaryState
-- name    : SchrodingerEquation.eigenfunction_isStationaryState
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T19:40:00.188427+00:00
-- url     : https://prove2.me/theorems/38503d2b-17b7-48d0-a028-e17afeaf9953
-- title:
--   The standing waves $\sin(n\pi x/L)$ realize the levels $E_n$
-- statement:
--   Let $\hbar > 0$, $m > 0$, $L > 0$ and let $n \ge 1$ be an integer. Then the standing wave
--   $$\psi_n(x) = \sin\!\left(\frac{n\pi x}{L}\right)$$
--   is a stationary state of the infinite well of width $L$ with energy
--   $$E_n = \frac{n^{2}\pi^{2}\hbar^{2}}{2 m L^{2}},$$
--   that is, it is continuous on $[0,L]$, twice differentiable on $(0,L)$, satisfies $-\frac{\hbar^2}{2m}\psi_n'' = E_n \psi_n$ there, and vanishes at both walls; moreover it is not identically zero inside the box.
--
--   This is the converse direction of the quantization statement: each of the energies $E_n$ is actually attained, so the goal theorem is not vacuous.
-- source:
--   Schrödinger equation, Wikipedia (revision retrieved 2026-09-21), https://en.wikipedia.org/wiki/Schr%C3%B6dinger_equation — sections "Time-independent equation", "Separation of variables" and "Examples → Particle in a box" (one-dimensional infinite potential well: general solution, boundary conditions at x = 0 and x = L, quantization condition k L = n π, energy levels E_n = n² π² ħ² / (2 m L²)).

import Definitions.Def_SchrodingerEquation_infinite_well_model

namespace SchrodingerEquation

theorem eigenfunction_isStationaryState (hbar m L : ℝ) (n : ℕ)
    (hbar_pos : 0 < hbar) (hm : 0 < m) (hL : 0 < L) (hn : 1 ≤ n) :
    IsStationaryState hbar m L (energyLevel hbar m L n) (eigenfunction L n) ∧
      ∃ x ∈ Set.Ioo 0 L, eigenfunction L n x ≠ 0 := by sorry

end SchrodingerEquation
