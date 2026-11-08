-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsModularForm_raiseLevel_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsModularForm_raiseLevel_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:46.819998+00:00
-- url     : https://prove2.me/theorems/c93bfee8-4a81-413c-8bf2-05e708f1e8b7
-- title:
--   Tanner Lifted Product: lps Modular Form raise Level apply
-- statement:
--   The Tanner Lifted Product construction uses the lps Modular Form raise Level apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L52-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L52-L54

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsModularForm_raiseLevel_apply (N L : ℕ) (hNL : N ∣ L)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    lpsModularForm_raiseLevel N L hNL f z=f z := by sorry
