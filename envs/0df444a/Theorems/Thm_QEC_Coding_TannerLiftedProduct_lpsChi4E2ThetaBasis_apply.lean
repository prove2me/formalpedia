-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2ThetaBasis_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2ThetaBasis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:50.892499+00:00
-- url     : https://prove2.me/theorems/7609a38a-8ee3-4471-8eac-6680f5c4391e
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Theta Basis apply
-- statement:
--   The Tanner Lifted Product construction uses the lps Chi4 E2 Theta Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L297-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L297-L298

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2ThetaBasis_apply (q : ℕ) [Fact q.Prime] (b : Fin 3) (z : ℍ) :
    lpsChi4E2ThetaBasis q b z=lpsChi4E2Dilate (q^b.val) (pow_pos (Fact.out : q.Prime).pos _) z := by sorry
