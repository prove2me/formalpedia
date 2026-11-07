-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeFinite_hasSum_mask
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeFinite_hasSum_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:17:56.564218+00:00
-- url     : https://prove2.me/theorems/77980171-409e-44d8-9499-536db7a94b48
-- title:
--   Tanner Lifted Product: lps Hecke Finite has Sum mask
-- statement:
--   Finite summation of actual convergent Fourier expansions filters out nonmultiples of p.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L83-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L83-L107

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeFinite_hasSum_mask (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => if p∣n then
      PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
        Function.Periodic.qParam (p:ℝ) (z:ℂ)^n else 0)
      ((p:ℂ)⁻¹*∑ j : Fin p,f (lpsHeckeUpperGL ℝ p (some j) • z)) := by sorry
