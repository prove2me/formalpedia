-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_commute_generatorSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_commute_generatorSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:28:05.371532+00:00
-- url     : https://prove2.me/theorems/2a78ffa6-e76a-4438-b85b-c38ef39e69cd
-- title:
--   Tanner Lifted Product: lps Finite Hecke Element commute generator Sum
-- statement:
--   Every finite LPS Hecke element commutes with the generator sum at which
--   its defining polynomial is evaluated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeReducedWords.lean#L21-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeReducedWords.lean#L21-L33

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_commute_generatorSum
    (a : LPSResiduePrime p) (n : ℕ) :
    Commute (lpsFiniteHeckeElement a n)
      (cayleyGeneratorSum (lpsQuaternionLabel a)) := by sorry
