-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicLocality_HammingWeight_leftRegular_cyclicBoundaryElement_row_le_two
-- name    : QEC.Coding.BalancedProduct.CyclicLocality.HammingWeight_leftRegular_cyclicBoundaryElement_row_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:53.27793+00:00
-- url     : https://prove2.me/theorems/02b3a053-1ae7-4729-832d-ed5f5825edbc
-- title:
--   Cyclic Locality: Hamming Weight left Regular cyclic Boundary Element row le two
-- statement:
--   Every row of the left-regular `1+x` cyclic boundary has weight at most
--   two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean#L112-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean#L112-L129

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicLocality
open QEC.Coding
open PKDistance
universe u v

theorem QEC.Coding.BalancedProduct.CyclicLocality.HammingWeight_leftRegular_cyclicBoundaryElement_row_le_two
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (x go : G) :
    HammingWeight (fun gi =>
      LiftedProduct.leftRegularMatrix (Cyclic.cyclicBoundaryElement x) go gi) ≤
      2 := by sorry
