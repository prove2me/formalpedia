-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_caseTwo_primitive_weight_lower_bound
-- name    : QEC.Coding.BalancedProduct.PKDistance.caseTwo_primitive_weight_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:04:43.27424+00:00
-- url     : https://prove2.me/theorems/678ded4f-59a3-41c1-8288-bd36f0ede6a8
-- title:
--   PKDistance: case Two primitive weight lower bound
-- statement:
--   The source's `w`-limited estimate, applied to the actual Case-2
--   remainder.  The premise is the concrete column-basis bound of the Tanner map;
--   the terminal BE20 construction proves it from its checked-in matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1129-L1157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1129-L1157

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

theorem QEC.Coding.BalancedProduct.PKDistance.caseTwo_primitive_weight_lower_bound
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
      h + cyclicShift (Cyclic.cyclicGenerator q) h)
    (w : Nat)
    (hColumnWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ w) :
    q ≤ HammingWeight (verticalPart z) + w * HammingWeight h := by sorry
