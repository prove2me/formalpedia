-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclic_card_le_HammingWeight_caseTwoRemainder
-- name    : QEC.Coding.BalancedProduct.PKDistance.cyclic_card_le_HammingWeight_caseTwoRemainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:03:18.888808+00:00
-- url     : https://prove2.me/theorems/f560c497-051f-440e-ab42-aee290ba851d
-- title:
--   PKDistance: cyclic card le Hamming Weight case Two Remainder
-- statement:
--   Concrete PK Case 2 conclusion before the Tanner locality estimate: after
--   removing the explicit horizontal primitive boundary, every non-boundary cycle
--   has a residual vertical word of weight at least `q`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1049-L1070
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1049-L1070

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w

theorem QEC.Coding.BalancedProduct.PKDistance.cyclic_card_le_HammingWeight_caseTwoRemainder
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1 (Cyclic.data q A) z = 0)
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleBoundaryCode.carrier)
    (h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q))
    (hu : horizontalPart z =
      h + cyclicShift (Cyclic.cyclicGenerator q) h) :
    q ≤ HammingWeight (caseTwoRemainder A z h) := by sorry
