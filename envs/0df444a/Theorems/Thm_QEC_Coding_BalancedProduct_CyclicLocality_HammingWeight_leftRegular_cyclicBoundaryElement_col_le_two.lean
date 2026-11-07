-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicLocality_HammingWeight_leftRegular_cyclicBoundaryElement_col_le_two
-- name    : QEC.Coding.BalancedProduct.CyclicLocality.HammingWeight_leftRegular_cyclicBoundaryElement_col_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:02:25.095729+00:00
-- url     : https://prove2.me/theorems/a8fb09ee-38c1-47ed-87c5-12329838e90e
-- title:
--   Cyclic Locality: Hamming Weight left Regular cyclic Boundary Element col le two
-- statement:
--   Every column of the left-regular `1+x` cyclic boundary has weight at most
--   two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean#L133-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean#L133-L150

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicLocality
open QEC.Coding
open PKDistance
universe u v

theorem QEC.Coding.BalancedProduct.CyclicLocality.HammingWeight_leftRegular_cyclicBoundaryElement_col_le_two
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (x gi : G) :
    HammingWeight (fun go =>
      LiftedProduct.leftRegularMatrix (Cyclic.cyclicBoundaryElement x) go gi) ≤
      2 := by sorry
