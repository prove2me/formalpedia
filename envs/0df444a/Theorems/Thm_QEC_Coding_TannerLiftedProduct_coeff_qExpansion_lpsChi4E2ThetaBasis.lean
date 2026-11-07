-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsChi4E2ThetaBasis
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsChi4E2ThetaBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:59.148361+00:00
-- url     : https://prove2.me/theorems/c0a9a18c-56ae-4b93-8e3d-a9b77c6c8b24
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Chi4 E2 Theta Basis
-- statement:
--   The Tanner Lifted Product construction uses the coeff q Expansion lps Chi4 E2 Theta Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L301-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L301-L305

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsChi4E2ThetaBasis (q : ℕ) [Fact q.Prime] (b : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4E2ThetaBasis q b))=
      if q^b.val∣n then -24*(ArithmeticFunction.sigma 1 (n/q^b.val):ℂ)*
        lpsChi4E2Character ((n/q^b.val:ℕ):ZMod 4) else 0 := by sorry
