-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralCuspHecke_polynomial_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegralCuspHecke_polynomial_coe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:36:39.987629+00:00
-- url     : https://prove2.me/theorems/4031bbdb-78b6-472c-9761-a9ab4bd400c6
-- title:
--   Tanner Lifted Product: lps Integral Cusp Hecke polynomial coe
-- statement:
--   Inclusion transports every integer polynomial action to the original complex operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean#L137-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean#L137-L149

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegralCuspHecke_polynomial_coe (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (P : ℤ[X]) (f : lpsIntegralCuspLattice N) :
    ((aeval (lpsIntegralCuspHecke N p hNp) P) f :
      CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) =
      (aeval (lpsCuspHeckeLinearMap N p hNp) (P.map (Int.castRingHom ℂ))) f.val := by sorry
