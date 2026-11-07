-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0HeckePrimePowerMatrix_recover
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_recover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:50:11.101143+00:00
-- url     : https://prove2.me/theorems/c235d055-c18e-413f-9838-4925046f660a
-- title:
--   Tanner Lifted Product: lps Gamma0 Hecke Prime Power Matrix recover
-- statement:
--   Reconstruct the actual prime-power Hecke image from its finite matrix and input coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L114-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L114-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_recover (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    (lpsGamma0CuspBasis N 2).equivFun.symm
      ((lpsGamma0HeckePrimePowerMatrix N p hNp r).mulVec
        ((lpsGamma0CuspBasis N 2).repr f)) = lpsHeckePrimePowerLinearMap N p hNp r f := by sorry
