-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeFinite_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeFinite_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:38.961214+00:00
-- url     : https://prove2.me/theorems/67637d15-c2e6-479d-bd0e-ba05ece854f3
-- title:
--   Tanner Lifted Product: lps Hecke Finite has Sum
-- statement:
--   Injective reindexing proves the actual finite part has coefficients a(p*n).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L110-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L110-L133

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeFinite_hasSum (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => PowerSeries.coeff (p*n) (UpperHalfPlane.qExpansion 1 f)*
      Function.Periodic.qParam 1 (z:ℂ)^n)
      ((p:ℂ)⁻¹*∑ j : Fin p,f (lpsHeckeUpperGL ℝ p (some j) • z)) := by sorry
