-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_eq_lpsAlternatingReducedWordElement
-- name    : QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_eq_lpsAlternatingReducedWordElement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:28:28.912197+00:00
-- url     : https://prove2.me/theorems/b627ca70-5bcf-4e22-a6f8-5d153e7b2639
-- title:
--   Tanner Lifted Product: lps Finite Hecke Element eq lps Alternating Reduced Word Element
-- statement:
--   The finite Hecke element is exactly the alternating sum of reduced-word
--   spheres `S_n + S_{n-2} + ⋯`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeReducedWords.lean#L67-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeReducedWords.lean#L67-L76

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_eq_lpsAlternatingReducedWordElement
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsFiniteHeckeElement a n =
      lpsAlternatingReducedWordElement a n := by sorry
