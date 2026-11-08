-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyRightTranslationSum_lps_eq_pglHecke
-- name    : QEC.Coding.TannerLiftedProduct.cayleyRightTranslationSum_lps_eq_pglHecke
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:42:53.189631+00:00
-- url     : https://prove2.me/theorems/878d803f-478b-4faf-9f7d-2c4d5a9dd88a
-- title:
--   Tanner Lifted Product: cayley Right Translation Sum lps eq pgl Hecke
-- statement:
--   Pullback along `PSL(2,q) → PGL(2,q)` intertwines the concrete LPS
--   adjacency sum with the norm-`p` quaternion-shell correspondence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCorrespondence.lean#L49-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCorrespondence.lean#L49-L65

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.cayleyRightTranslationSum_lps_eq_pglHecke
    (a : LPSResiduePrime p)
    (f : PGL(2, ZMod a.q) → ℂ)
    (g : PSL(2, ZMod a.q)) :
    cayleyRightTranslationSum (lpsQuaternionLabel a)
        (fun h => f (Matrix.ProjectiveSpecialLinearGroup.toPGL h)) g =
      cayleyRightTranslationSum (lpsPGLHeckeLabel a) f
        (Matrix.ProjectiveSpecialLinearGroup.toPGL g) := by sorry
