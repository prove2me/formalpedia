-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrefixTerm_backtrackingPrefixEquiv_symm
-- name    : QEC.Coding.TannerLiftedProduct.lpsPrefixTerm_backtrackingPrefixEquiv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:23:11.019382+00:00
-- url     : https://prove2.me/theorems/0104544a-e22d-4ccb-ba95-ec2dc5a9fb59
-- title:
--   Tanner Lifted Product: lps Prefix Term backtracking Prefix Equiv symm
-- statement:
--   The Tanner Lifted Product construction uses the lps Prefix Term backtracking Prefix Equiv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L506-L514
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L506-L514

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsPrefixTerm_backtrackingPrefixEquiv_symm
    (a : LPSResiduePrime p) (n : ℕ)
    (word : LPSReducedWord a.degreePrime.pos (n + 1)) :
    lpsPrefixTerm a
        ((lpsBacktrackingPrefixEquiv a.degreePrime n).symm word).1 =
      MonoidAlgebra.single
        (cayleyVectorWordProduct (lpsQuaternionLabel a) word.1.tail) 1 := by sorry
