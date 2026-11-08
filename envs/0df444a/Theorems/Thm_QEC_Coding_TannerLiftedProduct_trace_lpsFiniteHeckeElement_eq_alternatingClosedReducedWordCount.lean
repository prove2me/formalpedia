-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_lpsFiniteHeckeElement_eq_alternatingClosedReducedWordCount
-- name    : QEC.Coding.TannerLiftedProduct.trace_lpsFiniteHeckeElement_eq_alternatingClosedReducedWordCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:30:22.188365+00:00
-- url     : https://prove2.me/theorems/ef4c8ca0-4282-4eda-ad4f-b4766f2eb4e6
-- title:
--   Tanner Lifted Product: trace lps Finite Hecke Element eq alternating Closed Reduced Word Count
-- statement:
--   Regular trace form of the exact reduced-word identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeReducedWords.lean#L89-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeReducedWords.lean#L89-L97

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.trace_lpsFiniteHeckeElement_eq_alternatingClosedReducedWordCount
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
        (cayleyRightRegularRepresentation.asAlgebraHom
          (lpsFiniteHeckeElement a n)) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
        (lpsAlternatingClosedReducedWordCount a n : ℂ) := by sorry
