-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_complexWeightedNeighborSum_lps_eq_pglHecke
-- name    : QEC.Coding.TannerLiftedProduct.complexWeightedNeighborSum_lps_eq_pglHecke
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:02:50.182653+00:00
-- url     : https://prove2.me/theorems/08a790ef-7d20-4f9b-abab-d9f0580bdde1
-- title:
--   Tanner Lifted Product: complex Weighted Neighbor Sum lps eq pgl Hecke
-- statement:
--   Pointwise weighted adjacency on the concrete LPS Cayley graph is the
--   pullback of the projective norm-`p` Hecke correspondence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCorrespondence.lean#L69-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCorrespondence.lean#L69-L79

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.complexWeightedNeighborSum_lps_eq_pglHecke
    (a : LPSResiduePrime p)
    (f : PGL(2, ZMod a.q) → ℂ)
    (g : PSL(2, ZMod a.q)) :
    SmallSetExpansion.complexWeightedNeighborSum
        (rightCayleyGraph (lpsQuaternionLabel a))
        (fun h => f (Matrix.ProjectiveSpecialLinearGroup.toPGL h)) g =
      cayleyRightTranslationSum (lpsPGLHeckeLabel a) f
        (Matrix.ProjectiveSpecialLinearGroup.toPGL g) := by sorry
