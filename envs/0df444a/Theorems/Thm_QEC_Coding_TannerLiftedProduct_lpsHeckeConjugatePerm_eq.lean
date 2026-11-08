-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugatePerm_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeConjugatePerm_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:03:07.328087+00:00
-- url     : https://prove2.me/theorems/14e85169-3691-4d27-8a83-ae552f6d18ae
-- title:
--   Tanner Lifted Product: lps Hecke Conjugate Perm eq
-- statement:
--   The true upper-right intersection is the actual dilation-conjugate Gamma0(Np) action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L75-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L75-L95

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeConjugatePerm_eq (N p : ℕ) [Fact p.Prime] :
    (lpsEffectiveHeckeConjugateIntersection N p).map lpsEffectiveModularGroup.subtype =
      ((lpsEffectiveGamma0 (N*p)).map lpsEffectiveModularGroup.subtype).map
        (MulAut.conj (MulAction.toPerm (lpsHeckeUpperGL ℝ p none))).toMonoidHom := by sorry
