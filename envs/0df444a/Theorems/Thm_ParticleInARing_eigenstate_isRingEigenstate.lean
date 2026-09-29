-- Prove2me | Theorems.Thm_ParticleInARing_eigenstate_isRingEigenstate
-- name    : ParticleInARing.eigenstate_isRingEigenstate
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:39:19.667903+00:00
-- url     : https://prove2.me/theorems/78876f69-0e8f-40c1-aa5a-458272b90e0d
-- title:
--   $\psi_n$ is a stationary state of energy $E_n = n^2\hbar^2/2mR^2$
-- statement:
--   Let $\hbar, m, R$ be real with $m \neq 0$ and $R \neq 0$, and let $n$ be an integer. Then $\psi_n(\theta) = \frac{1}{\sqrt{2\pi}} e^{i n \theta}$ is a stationary state of energy $E_n = \dfrac{n^2 \hbar^2}{2 m R^2}$: it is twice continuously differentiable, it satisfies the periodic boundary condition, and
--
--   $$-\frac{\hbar^2}{2 m R^2}\, \psi_n''(\theta) = E_n\, \psi_n(\theta) \qquad \text{for all } \theta \in \mathbb{R}.$$
--
--   This is the source's statement that the eigenfunctions are $\psi(\theta) = \frac{1}{\sqrt{2\pi}} e^{\pm i n \theta}$ with eigenenergies $E_n = n^2\hbar^2/(2mR^2)$.
-- source:
--   Wikipedia, "Particle in a ring", https://en.wikipedia.org/wiki/Particle_in_a_ring (oldid 1318339663), sections "Wave function" and "Energy eigenvalues"

import Mathlib
import Definitions.Def_ParticleInARing_model

namespace ParticleInARing

theorem eigenstate_isRingEigenstate (hbar m R : ℝ) (hm : m ≠ 0) (hR : R ≠ 0) (n : ℤ) :
    IsRingEigenstate hbar m R (energy hbar m R n) (eigenstate n) := by sorry

end ParticleInARing
