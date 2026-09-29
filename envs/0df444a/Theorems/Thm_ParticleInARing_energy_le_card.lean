-- Prove2me | Theorems.Thm_ParticleInARing_energy_le_card
-- name    : ParticleInARing.energy_le_card
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:53:28.491586+00:00
-- url     : https://prove2.me/theorems/4b32344a-56cf-4017-acef-20d78e965659
-- title:
--   There are $2N+1$ states with energy up to $E_N$
-- statement:
--   Let $\hbar, m, R$ be positive reals and let $N$ be a natural number. Then exactly $2N + 1$ integers $n$ satisfy $E_n \le E_N$:
--
--   $$\#\left\{ n \in \mathbb{Z} \;:\; \frac{n^2\hbar^2}{2mR^2} \le \frac{N^2\hbar^2}{2mR^2} \right\} = 2N + 1 .$$
--
--   This is the source's count of the states with energies up to the level indexed by $n$; together with the two spin orientations of an electron it gives the $2 \times (2N+1) = 4N + 2$ electrons of Hückel's rule.
-- source:
--   Wikipedia, "Particle in a ring", https://en.wikipedia.org/wiki/Particle_in_a_ring (oldid 1318339663), sections "Wave function" and "Energy eigenvalues"

import Mathlib
import Definitions.Def_ParticleInARing_model

namespace ParticleInARing

theorem energy_le_card (hbar m R : ℝ) (hhbar : 0 < hbar) (hm : 0 < m) (hR : 0 < R) (N : ℕ) :
    {n : ℤ | energy hbar m R n ≤ energy hbar m R N}.ncard = 2 * N + 1 := by sorry

end ParticleInARing
