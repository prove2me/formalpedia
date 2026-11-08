-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordConsEquiv_symm_tail
-- name    : QEC.Coding.TannerLiftedProduct.lpsReducedWordConsEquiv_symm_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:22:38.049449+00:00
-- url     : https://prove2.me/theorems/a54a78ab-c098-4c7c-87d1-665baf98d1a4
-- title:
--   Tanner Lifted Product: lps Reduced Word Cons Equiv symm tail
-- statement:
--   The Tanner Lifted Product construction uses the lps Reduced Word Cons Equiv symm tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L229-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L229-L237

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsReducedWordConsEquiv_symm_tail
    (hp : p.Prime) (n : ℕ)
    (pair : {pair : LPSReducedWord hp.pos (n + 1) ×
        LPSGeneratorIndex p //
      pair.2 ∈ lpsReducedSuccessors hp.pos pair.1.1.head}) :
    ((lpsReducedWordConsEquiv hp n).symm pair).1.tail =
      pair.1.1.1 := by sorry
