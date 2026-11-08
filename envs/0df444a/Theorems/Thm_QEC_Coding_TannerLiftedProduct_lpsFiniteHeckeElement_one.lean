-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:51:54.089648+00:00
-- url     : https://prove2.me/theorems/cf8c9d26-f3fe-47b8-802d-ae505ee78c77
-- title:
--   Tanner Lifted Product: lps Finite Hecke Element one
-- statement:
--   The Tanner Lifted Product construction uses the lps Finite Hecke Element one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L92-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L92-L96

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

theorem QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_one
    (a : LPSResiduePrime p) :
    lpsFiniteHeckeElement a 1 =
      cayleyGeneratorSum (lpsQuaternionLabel a) := by sorry
