-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0HeckePrimePowerMatrix_coefficient
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:52:58.074221+00:00
-- url     : https://prove2.me/theorems/87a49589-38a5-4833-a23b-558558f0ef88
-- title:
--   Tanner Lifted Product: lps Gamma0 Hecke Prime Power Matrix coefficient
-- statement:
--   The reconstructed finite matrix image recovers the original prime-power Fourier coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L124-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L124-L133

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_coefficient (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1
      ((lpsGamma0CuspBasis N 2).equivFun.symm
        ((lpsGamma0HeckePrimePowerMatrix N p hNp r).mulVec
          ((lpsGamma0CuspBasis N 2).repr f)))) =
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 f) := by sorry
