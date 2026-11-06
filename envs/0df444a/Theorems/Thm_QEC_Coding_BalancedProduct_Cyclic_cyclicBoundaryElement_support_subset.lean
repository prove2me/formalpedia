-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_cyclicBoundaryElement_support_subset
-- name    : QEC.Coding.BalancedProduct.Cyclic.cyclicBoundaryElement_support_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:06:08.414617+00:00
-- url     : https://prove2.me/theorems/fa36d319-d9f4-4c93-9aed-646865fec233
-- title:
--   Cyclic: cyclic Boundary Element support subset
-- statement:
--   The support of `1 + x` is contained in its two displayed monomials.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L61-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean#L61-L73

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.Cyclic.cyclicBoundaryElement_support_subset
    {G : Type u} [Group G] [DecidableEq G] (x : G) :
    (cyclicBoundaryElement x).coeff.support ⊆ {1, x} := by sorry
