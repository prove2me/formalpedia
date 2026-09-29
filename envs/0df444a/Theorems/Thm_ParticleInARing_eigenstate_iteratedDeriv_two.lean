-- Prove2me | Theorems.Thm_ParticleInARing_eigenstate_iteratedDeriv_two
-- name    : ParticleInARing.eigenstate_iteratedDeriv_two
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:30:22.499371+00:00
-- url     : https://prove2.me/theorems/4ec45d56-a260-4aea-be4b-1be5dbbcd86f
-- title:
--   $\psi_n'' = -n^2 \psi_n$
-- statement:
--   For every integer $n$ and every $\theta \in \mathbb{R}$,
--
--   $$\psi_n''(\theta) = -n^2\, \psi_n(\theta),$$
--
--   where $\psi_n(\theta) = \frac{1}{\sqrt{2\pi}} e^{i n \theta}$. This is the differential identity behind the eigenvalue relation: applying $-\frac{\hbar^2}{2 m R^2} \frac{d^2}{d\theta^2}$ to $\psi_n$ returns $E_n \psi_n$.
-- source:
--   Wikipedia, "Particle in a ring", https://en.wikipedia.org/wiki/Particle_in_a_ring (oldid 1318339663), sections "Wave function" and "Energy eigenvalues"

import Mathlib
import Definitions.Def_ParticleInARing_model

namespace ParticleInARing

theorem eigenstate_iteratedDeriv_two (n : ℤ) (θ : ℝ) :
    iteratedDeriv 2 (eigenstate n) θ = (-((n : ℂ) ^ 2)) * eigenstate n θ := by sorry

end ParticleInARing
