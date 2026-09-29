-- Prove2me | Theorems.Thm_ParticleInARing_eigenstate_periodic
-- name    : ParticleInARing.eigenstate_periodic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:28:06.115986+00:00
-- url     : https://prove2.me/theorems/6b58e178-65b2-4ee2-9f5d-4a0b94269e3f
-- title:
--   $\psi_n$ satisfies the periodic boundary condition
-- statement:
--   For every integer $n$, the function $\psi_n(\theta) = \frac{1}{\sqrt{2\pi}} e^{i n \theta}$ is $2\pi$-periodic:
--
--   $$\psi_n(\theta + 2\pi) = \psi_n(\theta) \qquad \text{for all } \theta \in \mathbb{R}.$$
--
--   This is the requirement that the wave function be single-valued on the circle, which the source imposes as the boundary condition of the model.
-- source:
--   Wikipedia, "Particle in a ring", https://en.wikipedia.org/wiki/Particle_in_a_ring (oldid 1318339663), sections "Wave function" and "Energy eigenvalues"

import Mathlib
import Definitions.Def_ParticleInARing_model

namespace ParticleInARing

theorem eigenstate_periodic (n : ℤ) : IsRingPeriodic (eigenstate n) := by sorry

end ParticleInARing
