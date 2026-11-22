-- Prove2me | Theorems.Thm_ShiShallow_product_family_parseval_three
-- name    : ShiShallow.product_family_parseval_three
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T03:42:30.282716+00:00
-- url     : https://prove2.me/theorems/8dacc7a9-21f8-44c0-9a12-ed423784a150
-- title:
--   Parseval for any orthonormal family indexed by three blocks
-- statement:
--   For any orthonormal family of amplitude arrays on a register split into three blocks, indexed by the nested product of the three per-block index types, the sum over the family of the squared moduli of the overlaps with a state equals that state's squared norm. A dimension count: the family has as many members as the space has dimensions, so orthonormality forces it to be a basis. This is what forbids any component of a state entangled across the three blocks from escaping expansion in a product family.

import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

namespace ShiShallow

open ShiTensor

theorem product_family_parseval_three {m p q : ℕ}
    (V : (Bits m × Bits p) × Bits q → EuclideanSpace ℂ (Bits (m + p + q)))
    (hV : Orthonormal ℂ V) (x : EuclideanSpace ℂ (Bits (m + p + q))) :
    ∑ i : (Bits m × Bits p) × Bits q, ‖inner ℂ x (V i)‖ ^ 2 = ‖x‖ ^ 2 := by
  sorry

end ShiShallow
