-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPermConjugateFundamental
-- name    : QEC.Coding.TannerLiftedProduct.lpsPermConjugateFundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:00:49.775701+00:00
-- url     : https://prove2.me/theorems/d9f7d3bc-272f-4576-a88f-e058af6ed445
-- title:
--   Tanner Lifted Product: lps Perm Conjugate Fundamental
-- statement:
--   A real GL matrix sends a true subgroup domain to its genuine permutation-conjugate domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L24-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L24-L37

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsPermConjugateFundamental (H : Subgroup (Equiv.Perm ℍ))
    (A : GL (Fin 2) ℝ) {s : Set ℍ} (hs : IsFundamentalDomain H s volume) :
    IsFundamentalDomain (H.map (MulAut.conj (MulAction.toPerm A)).toMonoidHom)
      (A • s) volume := by sorry
