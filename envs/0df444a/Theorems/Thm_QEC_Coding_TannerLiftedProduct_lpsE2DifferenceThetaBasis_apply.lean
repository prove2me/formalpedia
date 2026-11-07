-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2DifferenceThetaBasis_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2DifferenceThetaBasis_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:27:47.00792+00:00
-- url     : https://prove2.me/theorems/91343266-2f60-4dbe-a793-50afb1760559
-- title:
--   Tanner Lifted Product: lps E2 Difference Theta Basis apply
-- statement:
--   The Tanner Lifted Product construction uses the lps E2 Difference Theta Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L278-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L278-L280

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2DifferenceThetaBasis_apply (q : ℕ) [Fact q.Prime] (a : Fin 5) (b : Fin 3) (z : ℍ) :
    lpsE2DifferenceThetaBasis q a b z=lpsE2Difference (2^a.val*q^b.val)
      (mul_pos (pow_pos (by decide) _) (pow_pos (Fact.out : q.Prime).pos _)) z := by sorry
