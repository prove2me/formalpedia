-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_action
-- name    : QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:04:09.648875+00:00
-- url     : https://prove2.me/theorems/6814ab47-b4c2-4015-b4b7-1f4d9fbc43ad
-- title:
--   Tanner Lifted Product: lps Finite Hecke Element action
-- statement:
--   The regular action of the concrete finite Hecke element is the Hecke
--   polynomial in the actual LPS Cayley adjacency element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L110-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L110-L119

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

theorem QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_action
    (a : LPSResiduePrime p) (n : ℕ) :
    cayleyRightRegularRepresentation.asAlgebraHom
        (lpsFiniteHeckeElement a n) =
      (lpsHeckePolynomial ℂ (p : ℂ) n).eval₂
        (algebraMap ℂ
          (Module.End ℂ (PSL(2, ZMod a.q) → ℂ)))
        (cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyGeneratorSum (lpsQuaternionLabel a))) := by sorry
