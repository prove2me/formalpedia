-- Prove2me | Theorems.Thm_SteinerSystem_quadruple_existence
-- name    : SteinerSystem.quadruple_existence
-- status  : Open
-- author  : @parclytaxel
-- created : 2026-11-11T05:58:58.91293+00:00
-- url     : https://prove2.me/theorems/e0d5b1bd-848e-4fc1-9c30-13169c51eb74
-- title:
--   Existence of Steiner quadruple systems
-- statement:
--   $(n,4,3)$-Steiner systems exist iff $n\ge4$ and $n\equiv2,4\bmod6$.
-- source:
--   Haim Hanani, "On quadruple systems", Canadian Journal of Mathematics, vol. 12 (1960), pp. 145-157. doi:10.4153/CJM-1960-013-3

import Definitions.Def_SteinerSystem

namespace SteinerSystem

theorem quadruple_existence {n : ℕ} :
    Nonempty (SteinerSystem n 4 3) ↔ 4 ≤ n ∧ (n % 6 = 2 ∨ n % 6 = 4) := by
  sorry

end SteinerSystem
