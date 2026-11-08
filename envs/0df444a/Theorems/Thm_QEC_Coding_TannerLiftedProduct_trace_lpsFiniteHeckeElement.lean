-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_lpsFiniteHeckeElement
-- name    : QEC.Coding.TannerLiftedProduct.trace_lpsFiniteHeckeElement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:53:01.200387+00:00
-- url     : https://prove2.me/theorems/20cf6e25-5177-4ca3-bd66-e7a70e0b08da
-- title:
--   Tanner Lifted Product: trace lps Finite Hecke Element
-- statement:
--   The trace of the actual finite LPS Hecke operator has been reduced to
--   one concrete identity coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L123-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L123-L130

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

theorem QEC.Coding.TannerLiftedProduct.trace_lpsFiniteHeckeElement
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
        (cayleyRightRegularRepresentation.asAlgebraHom
          (lpsFiniteHeckeElement a n)) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
        (lpsFiniteHeckeElement a n).coeff 1 := by sorry
