-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_middleCohomologyDistanceAtMost_lift
-- name    : QEC.Coding.ExpanderCodes.PK20.middleCohomologyDistanceAtMost_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:40:12.492198+00:00
-- url     : https://prove2.me/theorems/931a82b2-fe87-4669-a184-55d4970bc594
-- title:
--   PK20: middle Cohomology Distance At Most lift
-- statement:
--   PK20 Lemma `lm:LP-simple-cws` in the specialization used for the upper
--   distance bound: if the quotient matrix has fewer rows than columns, an actual
--   nontrivial cocycle of the lifted product has weight exactly the cyclic lift.
--   This is derived from the constant/augmentation chain-map splitting and is not
--   part of Proposition 1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L629-L714
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L629-L714

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.middleCohomologyDistanceAtMost_lift
    {G aRow aCol : Type}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (x : G) (hOdd : Odd (Fintype.card G))
    (hCard : Fintype.card aRow < Fintype.card aCol) :
    MiddleCohomologyDistanceAtMost
      (LiftedProduct.chainComplex (Cyclic.liftedProductData A x))
      (Fintype.card G) := by sorry
