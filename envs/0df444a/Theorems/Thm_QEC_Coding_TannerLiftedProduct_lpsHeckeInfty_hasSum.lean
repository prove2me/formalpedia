-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeInfty_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeInfty_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:08.26942+00:00
-- url     : https://prove2.me/theorems/bef7f1ea-38e7-49a4-b168-36f6c08c817d
-- title:
--   Tanner Lifted Product: lps Hecke Infty has Sum
-- statement:
--   The genuine affine dilation contributes exactly p times the dilation coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L136-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L136-L149

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeInfty_hasSum (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => (p:ℂ)*lpsModularDilationCoefficient
      (fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)) p n *
        Function.Periodic.qParam 1 (z:ℂ)^n)
      ((p:ℂ)*f (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • z)) := by sorry
