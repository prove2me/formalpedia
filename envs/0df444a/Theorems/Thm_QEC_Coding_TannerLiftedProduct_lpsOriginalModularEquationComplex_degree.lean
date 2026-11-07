-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularEquationComplex_degree
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularEquationComplex_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:02:03.410198+00:00
-- url     : https://prove2.me/theorems/6953f535-3bb1-41ce-8645-229eb947ac5c
-- title:
--   Tanner Lifted Product: lps Original Modular Equation Complex degree
-- statement:
--   The fixed original complex equation has degree at most the actual finite coset cardinal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L294-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L294-L307

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularEquationComplex_degree (N : ℕ) [NeZero N] (hN : 0<N) :
    (lpsOriginalModularEquationComplex N hN).natDegree≤Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by sorry
