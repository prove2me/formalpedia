-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordElement_add_two
-- name    : QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordElement_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:28:42.579772+00:00
-- url     : https://prove2.me/theorems/c4616cec-0d73-4c80-aaf2-6d4e676d2925
-- title:
--   Tanner Lifted Product: lps Alternating Reduced Word Element add two
-- statement:
--   Subtractive form of the alternating-sphere Hecke recurrence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeReducedWords.lean#L47-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeReducedWords.lean#L47-L63

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordElement_add_two
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsAlternatingReducedWordElement a (n + 2) =
      cayleyGeneratorSum (lpsQuaternionLabel a) *
          lpsAlternatingReducedWordElement a (n + 1) -
        algebraMap ℂ (MonoidAlgebra ℂ PSL(2, ZMod a.q)) (p : ℂ) *
          lpsAlternatingReducedWordElement a n := by sorry
