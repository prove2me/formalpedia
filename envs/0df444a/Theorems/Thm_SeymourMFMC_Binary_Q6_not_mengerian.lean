-- Prove2me | Theorems.Thm_SeymourMFMC_Binary_Q6_not_mengerian
-- name    : SeymourMFMC.Binary.Q6_not_mengerian
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T03:50:08.620649+00:00
-- url     : https://prove2.me/theorems/302d389e-fa90-43b6-be8b-7a842e015905
-- title:
--   Section 1, p. 193 — Q₆ is not Mengerian
-- statement:
--   The clutter
--
--   $$
--   Q_6 = \{\{1,3,5\}, \{1,4,6\}, \{2,3,6\}, \{2,4,5\}\}
--   $$
--
--   is not Mengerian: there is a weight map $w : E(Q_6) \to \mathbb Z^+$ for which no integral packing $q : Q_6 \to \mathbb Z^+$ satisfying the capacity constraints $\sum_{A \ni x} q(A) \le w(x)$ reaches the minimum weight of a member of $b(Q_6)$.
--
--   The paper states this together with the fact that $Q_6$ has the weak max-flow min-cut property. Only the "not Mengerian" half is formalized, as the weak property is not needed. With minor-closedness (2.3), it gives the "only if" direction of the main theorem.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 193, Section 1

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_Q6
import Definitions.Def_SeymourMFMC_Binary_IsMengerian

namespace SeymourMFMC.Binary

/-- Seymour 1977, Section 1, p. 193: the clutter `Q₆` is not Mengerian. -/
theorem Q6_not_mengerian : ¬ IsMengerian Q6 := by sorry

end SeymourMFMC.Binary
