-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_dualCycle_not_boundary_of_horizontalCohomologyProjection_ne_zero
-- name    : QEC.Coding.BalancedProduct.PKDistance.dualCycle_not_boundary_of_horizontalCohomologyProjection_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:06:31.979243+00:00
-- url     : https://prove2.me/theorems/ce241e7a-a213-4877-8d87-a845e97cee5c
-- title:
--   PKDistance: dual Cycle not boundary of horizontal Cohomology Projection ne zero
-- statement:
--   A cocycle whose selected horizontal cohomology class is nonzero becomes a
--   non-boundary cycle in the star-transposed lifted product.  This is the precise
--   logical-sector bridge needed before applying the two PK homology cases to the
--   dual complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2435-L2470
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2435-L2470

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

theorem QEC.Coding.BalancedProduct.PKDistance.dualCycle_not_boundary_of_horizontalCohomologyProjection_ne_zero
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCocycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalCohomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles.mkQ ⟨z, hz⟩) ≠ 0) :
    LiftedProductDuality.swapWord z ∉
      (LiftedProduct.chainComplex
        (LiftedProductDuality.dualData
          (Cyclic.data q A))).middleBoundaryCode.carrier := by sorry
