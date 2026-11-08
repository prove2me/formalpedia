-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_add_two
-- name    : QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:51:47.238353+00:00
-- url     : https://prove2.me/theorems/6368f92e-6eb6-4990-b649-5f28770d8358
-- title:
--   Tanner Lifted Product: lps Finite Hecke Element add two
-- statement:
--   The concrete LPS finite Hecke elements satisfy the source recurrence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L99-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L99-L106

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]
open scoped MatrixGroups
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_add_two
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsFiniteHeckeElement a (n + 2) =
      lpsFiniteHeckeElement a (n + 1) *
          cayleyGeneratorSum (lpsQuaternionLabel a) -
        algebraMap ℂ (MonoidAlgebra ℂ PSL(2, ZMod a.q)) (p : ℂ) *
          lpsFiniteHeckeElement a n := by sorry
