-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_nonzero_horizontalClass_caseOne_invGenerator_weight_bound
-- name    : QEC.Coding.BalancedProduct.PKDistance.nonzero_horizontalClass_caseOne_invGenerator_weight_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:05:57.710426+00:00
-- url     : https://prove2.me/theorems/7eb6c651-0489-4861-a43d-89e3d7f4fe95
-- title:
--   PKDistance: nonzero horizontal Class case One inv Generator weight bound
-- statement:
--   Source-shaped Case-1 completion in the inverse cyclic orientation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2324-L2387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2324-L2387

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

theorem QEC.Coding.BalancedProduct.PKDistance.nonzero_horizontalClass_caseOne_invGenerator_weight_bound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier)
    {d : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode d)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)⁻¹
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
            ⟨z, hz⟩) ≠ 0)
    (expansionNumerator expansionDenominator : Nat)
    (hd : 0 < d)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * d) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * d) ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by sorry
