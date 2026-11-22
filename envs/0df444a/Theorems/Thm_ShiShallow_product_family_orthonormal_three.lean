-- Prove2me | Theorems.Thm_ShiShallow_product_family_orthonormal_three
-- name    : ShiShallow.product_family_orthonormal_three
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T03:42:16.389717+00:00
-- url     : https://prove2.me/theorems/c8a96f04-3105-4a5f-8038-a26c3e9a9e4f
-- title:
--   A product of three orthonormal families is orthonormal
-- statement:
--   If u, v and w are orthonormal families of amplitude arrays on three registers, then their pointwise products, indexed by the nested product of the three index types, form an orthonormal family on the combined register. Normalisation factors across the three blocks, and for two distinct triple indices at least one block index differs, so that block's inner product vanishes and annihilates the whole term.

import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

namespace ShiShallow

open ShiTensor

theorem product_family_orthonormal_three {m p q : ℕ}
    (u : Bits m → EuclideanSpace ℂ (Bits m)) (v : Bits p → EuclideanSpace ℂ (Bits p))
    (w : Bits q → EuclideanSpace ℂ (Bits q))
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w) :
    Orthonormal ℂ (fun i : (Bits m × Bits p) × Bits q =>
      (WithLp.toLp 2 (fun y : Bits (m + p + q) =>
          u i.1.1 (leftBits (leftBits y)) * v i.1.2 (rightBits (leftBits y))
            * w i.2 (rightBits y)) : EuclideanSpace ℂ (Bits (m + p + q)))) := by
  sorry

end ShiShallow
