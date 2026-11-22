-- Prove2me | Theorems.Thm_VaidyaFarina_j_boost
-- name    : VaidyaFarina.j_boost
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T19:52:45.886701+00:00
-- url     : https://prove2.me/theorems/581cc068-a172-457a-8934-6b79622e8d57
-- title:
--   Eq. (16): field-dependent current transformation
-- statement:
--   **Eq. (16): the boosted current density is field-dependent.** The current counterpart of eq. (15): with the same definitions and boost laws, $4\pi(j'-j)=\partial_tE-\partial_{t'}E'$ at corresponding points, equivalently $\partial_t(E-E')-v\cdot\nabla E'$. Like eq. (15), the difference is controlled by the displacement-current term $-\partial_tE$ in eq. (14), so the sources cannot transform independently of the fields.
-- source:
--   A. Vaidya and C. Farina, Phys. Lett. A 153 (1991) 265-267, https://doi.org/10.1016/0375-9601(91)90940-A, p. 266, eq. (16)

import Mathlib
import Definitions.Def_vf_defs

namespace VaidyaFarina
theorem j_boost(E H : ST → (Fin 3 → ℝ)) (v : Fin 3 → ℝ)
  (hE : ContDiff ℝ 1 E) (hH : ContDiff ℝ 1 H) (p : ST) :
  (4 * Real.pi) • (jOf (boostE v E H) (boostH v H) p - jOf E H (p.1 + p.2 • v, p.2))
    = fun i => dT (fun q => E q i) (p.1 + p.2 • v, p.2) - dT (fun q => boostE v E H q i) p := by sorry
end VaidyaFarina
