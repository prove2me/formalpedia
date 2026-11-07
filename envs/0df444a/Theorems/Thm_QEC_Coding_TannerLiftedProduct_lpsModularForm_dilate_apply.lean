-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsModularForm_dilate_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsModularForm_dilate_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:27:44.673526+00:00
-- url     : https://prove2.me/theorems/7e6a7f37-43d1-4af4-ac19-16643530df63
-- title:
--   Tanner Lifted Product: lps Modular Form dilate apply
-- statement:
--   The Tanner Lifted Product construction uses the lps Modular Form dilate apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L152-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L152-L154

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsModularForm_dilate_apply (N m : ℕ) [NeZero N] (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    lpsModularForm_dilate N m hm f z=f (lpsE2AffineMatrix m hm 0 • z) := by sorry
