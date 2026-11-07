-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsModularForm_dilate_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsModularForm_dilate_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:14:39.514695+00:00
-- url     : https://prove2.me/theorems/df6e5de7-4258-4876-afcf-427a0d5f72f5
-- title:
--   Tanner Lifted Product: lps Modular Form dilate has Sum
-- statement:
--   The Tanner Lifted Product construction uses the lps Modular Form dilate has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L161-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L161-L189

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsModularForm_dilate_hasSum (N m : ℕ) [NeZero N] (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => lpsModularDilationCoefficient
      (fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)) m n *
        Function.Periodic.qParam 1 (z:ℂ)^n) (lpsModularForm_dilate N m hm f z) := by sorry
