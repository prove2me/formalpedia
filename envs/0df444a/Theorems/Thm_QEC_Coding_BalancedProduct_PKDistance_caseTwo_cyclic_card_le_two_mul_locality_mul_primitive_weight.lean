-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_caseTwo_cyclic_card_le_two_mul_locality_mul_primitive_weight
-- name    : QEC.Coding.BalancedProduct.PKDistance.caseTwo_cyclic_card_le_two_mul_locality_mul_primitive_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:04:45.100206+00:00
-- url     : https://prove2.me/theorems/b12ab138-a884-46fc-8d85-8a827bad5615
-- title:
--   PKDistance: case Two cyclic card le two mul locality mul primitive weight
-- statement:
--   If the concrete vertical block is smaller than half a cyclic fibre, the
--   normalized primitive must carry the complementary source-scale weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1161-L1185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1161-L1185

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

theorem QEC.Coding.BalancedProduct.PKDistance.caseTwo_cyclic_card_le_two_mul_locality_mul_primitive_weight
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
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ w)
    (hVerticalHalf : 2 * HammingWeight (verticalPart z) ≤ q) :
    q ≤ 2 * w * HammingWeight h := by sorry
