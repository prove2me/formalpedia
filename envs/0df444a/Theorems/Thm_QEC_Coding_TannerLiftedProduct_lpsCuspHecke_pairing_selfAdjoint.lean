-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHecke_pairing_selfAdjoint
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHecke_pairing_selfAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:04:31.021526+00:00
-- url     : https://prove2.me/theorems/1642ab48-f969-475f-bd84-ad25e57b30b8
-- title:
--   Tanner Lifted Product: lps Cusp Hecke pairing self Adjoint
-- statement:
--   The original unnormalized prime-away-level cusp Hecke operator is Petersson self-adjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonAdjunction.lean#L83-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonAdjunction.lean#L83-L89

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonAdjunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHecke_pairing_selfAdjoint (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      lpsCuspPeterssonPairing N f (lpsCuspHeckeLinearMap N p hNp g) := by sorry
