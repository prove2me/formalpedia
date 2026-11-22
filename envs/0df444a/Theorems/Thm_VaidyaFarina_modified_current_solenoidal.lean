-- Prove2me | Theorems.Thm_VaidyaFarina_modified_current_solenoidal
-- name    : VaidyaFarina.modified_current_solenoidal
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T19:53:43.030889+00:00
-- url     : https://prove2.me/theorems/4623088b-c7f4-4f0c-b967-3af545d48f89
-- title:
--   Solenoidality of the modified current
-- statement:
--   **Solenoidality of the modified current (p. 266).** In the modified theory $j=(\nabla\times H)/4\pi$, so $\nabla\cdot j=0$. Vaidya–Farina draw the consequence that "the total charge is invariant and can be factored out" of the force law, and that the electric field cannot interact with a charge density in this limit.
-- source:
--   A. Vaidya and C. Farina, Phys. Lett. A 153 (1991) 265-267, https://doi.org/10.1016/0375-9601(91)90940-A, p. 266, discussion after eq. (19)

import Mathlib
import Definitions.Def_vf_defs

namespace VaidyaFarina
theorem modified_current_solenoidal(H : ST → (Fin 3 → ℝ)) (hH : ContDiff ℝ 2 H) (p : ST) :
  vdiv (jMod H) p = 0 := by sorry
end VaidyaFarina
