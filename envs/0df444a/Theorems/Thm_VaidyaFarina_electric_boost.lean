-- Prove2me | Theorems.Thm_VaidyaFarina_electric_boost
-- name    : VaidyaFarina.electric_boost
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T19:51:21.310023+00:00
-- url     : https://prove2.me/theorems/4ac79658-97b4-4f81-ae52-55598db49c97
-- title:
--   Eq. (10): boost transformation of the electric field
-- statement:
--   **Eq. (10): the electric field transforms as $E'=E+v\times H$.** The electric field is defined by the force decomposition $F_i=E_i+\varepsilon_{ijk}\dot x_jH_k$ (eq. (3)). Under a Galilean boost the force is invariant, $F'=F$ (eq. (9)), the velocity shifts by the central vector $v$, and $H'=H$ (eq. (8)). Solving the decomposition for the boosted electric field gives $E'_i=E_i+\varepsilon_{ijk}v_jH_k$. This is the algebraic content of eq. (10).
-- source:
--   A. Vaidya and C. Farina, Phys. Lett. A 153 (1991) 265-267, https://doi.org/10.1016/0375-9601(91)90940-A, p. 265, eq. (10)

import Mathlib
import Definitions.Def_vf_defs

namespace VaidyaFarina
theorem electric_boost(A : Type*) [Ring A] [Algebra ℂ A] (F vel H : Fin 3 → A) (v : Fin 3 → ℂ) :
  elecOf F (fun i => vel i - algebraMap ℂ A (v i)) H
    = fun i => elecOf F vel H i + crossA (fun j => algebraMap ℂ A (v j)) H i := by sorry
end VaidyaFarina
