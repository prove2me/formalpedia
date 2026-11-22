-- Prove2me | Theorems.Thm_SpherePackingBeyond_D4_isUnitPacking
-- name    : SpherePackingBeyond.D4_isUnitPacking
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T22:38:26.304175+00:00
-- url     : https://prove2.me/theorems/cf3746e9-2c35-4e16-9a9f-805f233f3b5e
-- title:
--   $\sqrt{2}\,D_4$ is a unit packing
-- statement:
--   The scaled checkerboard set `D4centers` $= \sqrt{2}\,D_4$ is a unit packing: any two distinct centers are at distance at least $2$. This holds because the shortest nonzero vector of $D_4$ has length $\sqrt{2}$, so distinct points of $\sqrt{2}\,D_4$ are at distance $\ge \sqrt{2}\cdot\sqrt{2} = 2$. It is the packing hypothesis needed for the density computation and for the definition of $\Delta_4$.
--
--   **Formalization Note.** `IsUnitPacking` is the separation-$2$ predicate from `Def_TenChallenges_SpherePacking`.
-- source:
--   Conway & Sloane, Sphere Packings, Lattices and Groups, 3rd ed., Springer 1999, Table I.1 (pp. xix-xx), https://doi.org/10.1007/978-1-4757-6568-7 (D4 minimal norm 2, Ch. 4 §7.1)

import Mathlib
import Definitions.Def_TenChallenges_SpherePacking
import Definitions.Def_SpherePackingBeyond_D4
open scoped BigOperators

namespace SpherePackingBeyond
theorem D4_isUnitPacking : IsUnitPacking D4centers := by sorry
end SpherePackingBeyond
