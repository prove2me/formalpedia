-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_finrank_middleHomology_bounds
-- name    : QEC.Coding.ExpanderCodes.PK20.finrank_middleHomology_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:40:05.423071+00:00
-- url     : https://prove2.me/theorems/1bddf04f-ab5e-4dd3-8c81-a2c3f0fc658a
-- title:
--   PK20: finrank middle Homology bounds
-- statement:
--   Exact finite dimension window used by PK20 Theorem 1.  Its lower half is
--   the quotient-Tanner injection and its upper half is forced by the two cyclic
--   `1+x` blocks; neither bound is included in Proposition 1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L448-L462
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L448-L462

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.finrank_middleHomology_bounds
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hOdd : Odd q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Fintype.card aCol - Fintype.card aRow ≤
        Module.finrank (ZMod 2)
          (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology ∧
      Module.finrank (ZMod 2)
          (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology ≤
        Fintype.card aCol + Fintype.card aRow := by sorry
