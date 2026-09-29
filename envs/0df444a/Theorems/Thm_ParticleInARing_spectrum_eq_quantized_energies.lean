-- Prove2me | Theorems.Thm_ParticleInARing_spectrum_eq_quantized_energies
-- name    : ParticleInARing.spectrum_eq_quantized_energies
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:55:28.692314+00:00
-- url     : https://prove2.me/theorems/d6442834-b263-4706-8ae2-5559acc0fa56
-- title:
--   The ring spectrum is exactly $\{\, n^2\hbar^2/(2mR^2) : n \in \mathbb{Z} \,\}$
-- statement:
--   Let $\hbar, m, R$ be positive reals and let $E$ be real. Then there exists a wave function $\psi : \mathbb{R} \to \mathbb{C}$ which is not identically zero, is twice continuously differentiable, satisfies the periodic boundary condition $\psi(\theta + 2\pi) = \psi(\theta)$, and solves
--
--   $$-\frac{\hbar^2}{2 m R^2}\, \psi''(\theta) = E\, \psi(\theta) \qquad (\theta \in \mathbb{R})$$
--
--   if and only if
--
--   $$E = \frac{n^2 \hbar^2}{2 m R^2} \quad \text{for some } n \in \mathbb{Z}.$$
--
--   In other words, the energy levels of a free particle on a ring are quantized, and the admissible energies are exactly the values $E_n$, $n = 0, \pm 1, \pm 2, \dots$. The easy direction is the construction of the eigenfunctions $\psi_n$; the substantive direction excludes every other real $E$, in particular all $E < 0$ and all positive $E$ whose wave number is not an integer.
-- source:
--   Wikipedia, "Particle in a ring", https://en.wikipedia.org/wiki/Particle_in_a_ring (oldid 1318339663), sections "Wave function" and "Energy eigenvalues"

import Mathlib
import Definitions.Def_ParticleInARing_model

namespace ParticleInARing

theorem spectrum_eq_quantized_energies (hbar m R : ℝ) (hhbar : 0 < hbar) (hm : 0 < m)
    (hR : 0 < R) (E : ℝ) :
    (∃ ψ : ℝ → ℂ, (∃ θ : ℝ, ψ θ ≠ 0) ∧ IsRingEigenstate hbar m R E ψ) ↔
      ∃ n : ℤ, E = energy hbar m R n := by sorry

end ParticleInARing
