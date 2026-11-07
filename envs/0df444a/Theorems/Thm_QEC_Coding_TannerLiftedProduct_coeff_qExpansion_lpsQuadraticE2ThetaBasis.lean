-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsQuadraticE2ThetaBasis
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsQuadraticE2ThetaBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:01.400741+00:00
-- url     : https://prove2.me/theorems/ed7bd814-2947-40c1-9d04-9084b3a94ea7
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Quadratic E2 Theta Basis
-- statement:
--   The Tanner Lifted Product construction uses the coeff q Expansion lps Quadratic E2 Theta Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L323-L328
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L323-L328

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsQuadraticE2ThetaBasis (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : Fin 5) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsQuadraticE2ThetaBasis q hq2 a))=
      if 2^a.val∣n then -24*(ArithmeticFunction.sigma 1 (n/2^a.val):ℂ)*
        lpsQuadraticE2Character q ((n/2^a.val:ℕ):ZMod q) else 0 := by sorry
