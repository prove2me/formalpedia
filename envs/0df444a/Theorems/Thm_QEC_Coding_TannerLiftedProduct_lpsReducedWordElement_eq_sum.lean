-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordElement_eq_sum
-- name    : QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:25:30.272706+00:00
-- url     : https://prove2.me/theorems/adb75d8f-db69-479b-89bb-9cfe3c9a9afc
-- title:
--   Tanner Lifted Product: lps Reduced Word Element eq sum
-- statement:
--   Subtype-sum presentation of the reduced-word sphere.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L327-L339
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L327-L339

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_eq_sum
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsReducedWordElement a n =
      ∑ word : LPSReducedWord a.degreePrime.pos n,
        MonoidAlgebra.single
          (cayleyVectorWordProduct (lpsQuaternionLabel a) word.1) 1 := by sorry
