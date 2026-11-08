-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_add_two_left
-- name    : QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_add_two_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:28:19.540633+00:00
-- url     : https://prove2.me/theorems/e4424e9f-889f-4245-9d1a-3375f3531259
-- title:
--   Tanner Lifted Product: lps Finite Hecke Element add two left
-- statement:
--   Left-handed form of the finite Hecke recurrence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeReducedWords.lean#L36-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeReducedWords.lean#L36-L44

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_add_two_left
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsFiniteHeckeElement a (n + 2) =
      cayleyGeneratorSum (lpsQuaternionLabel a) *
          lpsFiniteHeckeElement a (n + 1) -
        algebraMap ℂ (MonoidAlgebra ℂ PSL(2, ZMod a.q)) (p : ℂ) *
          lpsFiniteHeckeElement a n := by sorry
