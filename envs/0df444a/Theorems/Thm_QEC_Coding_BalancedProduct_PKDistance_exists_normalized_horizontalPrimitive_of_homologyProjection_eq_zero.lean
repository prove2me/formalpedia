-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_normalized_horizontalPrimitive_of_homologyProjection_eq_zero
-- name    : QEC.Coding.BalancedProduct.PKDistance.exists_normalized_horizontalPrimitive_of_homologyProjection_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:06:03.088671+00:00
-- url     : https://prove2.me/theorems/560af79c-fa69-44e0-83f0-bcae48517086
-- title:
--   PKDistance: exists normalized horizontal Primitive of homology Projection eq zero
-- statement:
--   The zero-horizontal-projection branch of a concrete lifted-product cycle
--   has the normalized cyclic primitive required by PK20 Case 2.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1805-L1829
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1805-L1829

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

theorem QEC.Coding.BalancedProduct.PKDistance.exists_normalized_horizontalPrimitive_of_homologyProjection_eq_zero
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) = 0) :
    ∃ h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q),
      horizontalPart z =
        h + cyclicShift (Cyclic.cyclicGenerator q) h ∧
      ∀ c, 2 * fibreWeight h c ≤ q := by sorry
