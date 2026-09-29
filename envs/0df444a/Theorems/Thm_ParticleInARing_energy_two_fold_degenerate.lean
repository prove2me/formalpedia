-- Prove2me | Theorems.Thm_ParticleInARing_energy_two_fold_degenerate
-- name    : ParticleInARing.energy_two_fold_degenerate
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:49:36.480984+00:00
-- url     : https://prove2.me/theorems/3ee78cf3-633d-477a-a0dc-839e7c7666fa
-- title:
--   Two-fold degeneracy of every level with $n \neq 0$
-- statement:
--   Let $\hbar, m, R$ be real and let $n$ be a nonzero integer. Then
--
--   $$E_{-n} = E_n \qquad \text{and} \qquad \psi_n, \psi_{-n} \text{ are linearly independent over } \mathbb{C}.$$
--
--   That is, the two eigenfunctions $\frac{1}{\sqrt{2\pi}} e^{\pm i n \theta}$ carry the same energy but are genuinely different states, which is the source's assertion that there are two degenerate quantum states for every value of $n > 0$.
-- source:
--   Wikipedia, "Particle in a ring", https://en.wikipedia.org/wiki/Particle_in_a_ring (oldid 1318339663), sections "Wave function" and "Energy eigenvalues"

import Mathlib
import Definitions.Def_ParticleInARing_model

namespace ParticleInARing

theorem energy_two_fold_degenerate (hbar m R : ℝ) (n : ℤ) (hn : n ≠ 0) :
    energy hbar m R (-n) = energy hbar m R n ∧
      LinearIndependent ℂ ![eigenstate n, eigenstate (-n)] := by sorry

end ParticleInARing
