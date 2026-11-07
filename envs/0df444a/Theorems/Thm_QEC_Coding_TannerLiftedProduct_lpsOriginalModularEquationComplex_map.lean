-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularEquationComplex_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularEquationComplex_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:55:24.576886+00:00
-- url     : https://prove2.me/theorems/8b00c8c1-394e-4954-81d4-f31b6b4410ee
-- title:
--   Tanner Lifted Product: lps Original Modular Equation Complex map
-- statement:
--   Specializing the coefficient variable gives the actual Lagrange interpolant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L264-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L264-L276

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularEquationComplex_map (N : ℕ) [NeZero N] (hN : 0<N) (x : ℂ) :
    (lpsOriginalModularEquationComplex N hN).map (Polynomial.evalRingHom x)=
      Lagrange.interpolate (Finset.univ:Finset (Fin ((Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))+1)))
        (fun i => (i.val:ℂ))
        (fun i => (lpsOriginalModularNormCoefficient N hN (i.val:ℂ)).eval x) := by sorry
