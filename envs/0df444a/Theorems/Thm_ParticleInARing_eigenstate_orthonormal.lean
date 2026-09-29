-- Prove2me | Theorems.Thm_ParticleInARing_eigenstate_orthonormal
-- name    : ParticleInARing.eigenstate_orthonormal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:42:41.673985+00:00
-- url     : https://prove2.me/theorems/b008bb27-6e1e-4bdd-9e7a-0aee4cd77b1f
-- title:
--   Orthonormality: $\int_0^{2\pi} \overline{\psi_j}\psi_n = \delta_{jn}$
-- statement:
--   For all integers $j$ and $n$,
--
--   $$\int_0^{2\pi} \overline{\psi_j(\theta)}\, \psi_n(\theta)\, d\theta = \begin{cases} 1 & j = n \\ 0 & j \neq n \end{cases}$$
--
--   where $\psi_n(\theta) = \frac{1}{\sqrt{2\pi}} e^{i n \theta}$. The energy eigenfunctions of the particle on a ring therefore form an orthonormal family on $[0, 2\pi]$ — the classical Fourier system, which is the precise sense in which expanding a ring wave function in eigenstates is the Fourier expansion of a periodic function.
-- source:
--   Wikipedia, "Particle in a ring", https://en.wikipedia.org/wiki/Particle_in_a_ring (oldid 1318339663), sections "Wave function" and "Energy eigenvalues"

import Mathlib
import Definitions.Def_ParticleInARing_model

namespace ParticleInARing

theorem eigenstate_orthonormal (j n : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), (starRingEnd ℂ) (eigenstate j θ) * eigenstate n θ =
      if j = n then 1 else 0 := by sorry

end ParticleInARing
