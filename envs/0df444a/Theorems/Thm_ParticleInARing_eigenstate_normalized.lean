-- Prove2me | Theorems.Thm_ParticleInARing_eigenstate_normalized
-- name    : ParticleInARing.eigenstate_normalized
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:29:21.416991+00:00
-- url     : https://prove2.me/theorems/7d31c5cb-e5a2-4842-a4e5-b7ef43e0fc58
-- title:
--   $\int_0^{2\pi} |\psi_n|^2 = 1$
-- statement:
--   For every integer $n$, the function $\psi_n(\theta) = \frac{1}{\sqrt{2\pi}} e^{i n \theta}$ is normalized over one period:
--
--   $$\int_0^{2\pi} |\psi_n(\theta)|^2\, d\theta = 1.$$
--
--   This is the normalization condition the source imposes on the wave functions, and it is what fixes the prefactor $1/\sqrt{2\pi}$.
-- source:
--   Wikipedia, "Particle in a ring", https://en.wikipedia.org/wiki/Particle_in_a_ring (oldid 1318339663), sections "Wave function" and "Energy eigenvalues"

import Mathlib
import Definitions.Def_ParticleInARing_model

namespace ParticleInARing

theorem eigenstate_normalized (n : ℤ) : IsRingNormalized (eigenstate n) := by sorry

end ParticleInARing
