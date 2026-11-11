-- Prove2me | Theorems.Thm_SteinerSystem_triple_existence
-- name    : SteinerSystem.triple_existence
-- status  : Open
-- author  : @parclytaxel
-- created : 2026-11-11T05:58:03.664195+00:00
-- url     : https://prove2.me/theorems/8b02df6c-c858-42a1-ae7b-3967212d9a25
-- title:
--   Existence of Steiner triple systems
-- statement:
--   $(n,3,2)$-Steiner systems exist iff $n\ge3$ and $n\equiv1,3\bmod6$.
-- source:
--   Thoralf Skolem, "Some Remarks on the Triple Systems of Steiner", Mathematica Scandinavica, vol. 6, pp. 273–280, Dec. 1958. doi: 10.7146/math.scand.a-10551

import Definitions.Def_SteinerSystem

namespace SteinerSystem

theorem triple_existence {n : ℕ} :
    Nonempty (SteinerSystem n 3 2) ↔ 3 ≤ n ∧ (n % 6 = 1 ∨ n % 6 = 3) := by
  sorry

end SteinerSystem
