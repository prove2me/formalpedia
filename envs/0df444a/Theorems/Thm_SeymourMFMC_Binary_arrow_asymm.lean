-- Prove2me | Theorems.Thm_SeymourMFMC_Binary_arrow_asymm
-- name    : SeymourMFMC.Binary.arrow_asymm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T04:36:55.673252+00:00
-- url     : https://prove2.me/theorems/a94b950a-c3fa-4073-b989-f80be60a7149
-- title:
--   (4.3) — in a critical MBC, x → y implies y ↛ x
-- statement:
--   Let $\mathbf L$ be a critical Mengerian binary clutter and $x, y \in E(\mathbf L)$. If $x \to y$, then
--
--   $$
--   y \not\to x .
--   $$
--
--   The relation $\to$ is therefore antisymmetric on critical Mengerian binary clutters, whereas $Q_6$ has pairs with $x \to y$ and $y \to x$. This asymmetry is used in (4.5).
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 206, (4.3)

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsMengerian
import Definitions.Def_SeymourMFMC_Binary_IsCritical
import Definitions.Def_SeymourMFMC_Binary_Arrow

namespace SeymourMFMC.Binary

/-- Seymour 1977, (4.3), p. 206: if `L` is a critical Mengerian binary clutter, `x, y ∈ E(L)`
and `x → y`, then `y ↛ x`. -/
theorem arrow_asymm {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L) (hcrit : IsCritical L)
    (x y : α) (hx : x ∈ ground L) (hy : y ∈ ground L) (hxy : Arrow L x y) :
    ¬ Arrow L y x := by sorry

end SeymourMFMC.Binary
