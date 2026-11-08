-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyVectorWordProduct_lpsReducedWordPrefixEquiv
-- name    : QEC.Coding.TannerLiftedProduct.cayleyVectorWordProduct_lpsReducedWordPrefixEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:22:48.203336+00:00
-- url     : https://prove2.me/theorems/37d3ea66-1bd8-4f37-a171-003c24bb3975
-- title:
--   Tanner Lifted Product: cayley Vector Word Product lps Reduced Word Prefix Equiv
-- statement:
--   The Tanner Lifted Product construction uses the cayley Vector Word Product lps Reduced Word Prefix Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L341-L351
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L341-L351

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.cayleyVectorWordProduct_lpsReducedWordPrefixEquiv
    (a : LPSResiduePrime p) (n : ℕ)
    (pair : {pair : LPSGeneratorIndex p ×
        LPSReducedWord a.degreePrime.pos (n + 1) //
      pair.1 ∈ lpsReducedSuccessors
        a.degreePrime.pos pair.2.1.head}) :
    cayleyVectorWordProduct (lpsQuaternionLabel a)
        (lpsReducedWordPrefixEquiv a.degreePrime n pair).1 =
      lpsQuaternionLabel a pair.1.1 *
        cayleyVectorWordProduct (lpsQuaternionLabel a) pair.1.2.1 := by sorry
