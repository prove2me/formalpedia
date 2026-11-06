-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_starTranspose_cyclicBoundaryMatrix
-- name    : QEC.Coding.BalancedProduct.Cyclic.starTranspose_cyclicBoundaryMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:06:16.430484+00:00
-- url     : https://prove2.me/theorems/6c7fb1ce-f259-4c9c-a368-4081cbc61d9f
-- title:
--   Cyclic: star Transpose cyclic Boundary Matrix
-- statement:
--   The star-transpose of the one-column cyclic boundary reverses the chosen
--   orientation and makes no other change.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L135-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L135-L142

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.Cyclic.starTranspose_cyclicBoundaryMatrix
    {G : Type u} [Group G] (x : G) :
    LiftedProduct.starTranspose (cyclicBoundaryMatrix x) =
      cyclicBoundaryMatrix x⁻¹ := by sorry
