-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPGLHeckeLabel_eq_toPGL
-- name    : QEC.Coding.TannerLiftedProduct.lpsPGLHeckeLabel_eq_toPGL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:42:42.467086+00:00
-- url     : https://prove2.me/theorems/42c3662a-6518-4880-af03-ea459a2b89ca
-- title:
--   Tanner Lifted Product: lps PGLHecke Label eq to PGL
-- statement:
--   The Hecke label agrees exactly with the projectivization of the concrete
--   `PSL(2,q)` graph label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCorrespondence.lean#L38-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCorrespondence.lean#L38-L45

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsPGLHeckeLabel_eq_toPGL
    (a : LPSResiduePrime p) (t : LPSGeneratorIndex p) :
    lpsPGLHeckeLabel a t =
      Matrix.ProjectiveSpecialLinearGroup.toPGL
        (lpsQuaternionLabel a t) := by sorry
