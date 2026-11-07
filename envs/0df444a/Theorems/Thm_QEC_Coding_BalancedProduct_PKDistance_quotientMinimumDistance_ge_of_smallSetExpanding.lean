-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_quotientMinimumDistance_ge_of_smallSetExpanding
-- name    : QEC.Coding.BalancedProduct.PKDistance.quotientMinimumDistance_ge_of_smallSetExpanding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:02:49.837196+00:00
-- url     : https://prove2.me/theorems/1277e554-3490-4726-ac43-07c735084f8c
-- title:
--   PKDistance: quotient Minimum Distance ge of small Set Expanding
-- statement:
--   Small-set expansion of the lifted Tanner action forces the attained
--   quotient Tanner distance above every radius whose constant-orbit lift is
--   covered by the expansion hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L563-L605
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L563-L605

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

theorem QEC.Coding.BalancedProduct.PKDistance.quotientMinimumDistance_ge_of_smallSetExpanding
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    {actualDistance distanceLowerBound expansionNumerator
      expansionDenominator : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode
        actualDistance)
    (hNumeratorPositive : 0 < expansionNumerator)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (Fintype.card G * distanceLowerBound)
      expansionNumerator expansionDenominator) :
    distanceLowerBound ≤ actualDistance := by sorry
