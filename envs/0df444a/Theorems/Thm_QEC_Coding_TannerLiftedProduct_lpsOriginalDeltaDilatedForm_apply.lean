-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedForm_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedForm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:34:51.576364+00:00
-- url     : https://prove2.me/theorems/ef349190-b5a0-4528-8b7a-114ab1f21e0f
-- title:
--   Tanner Lifted Product: lps Original Delta Dilated Form apply
-- statement:
--   Pinned Mathlib weight12 slash gives N^11*Delta(Ntau); used to prove the actual form nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L163-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L163-L168

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedForm_apply (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalDeltaDilatedForm N hN τ=(N:ℂ)^11*
      ModularForm.discriminant (lpsE2AffineMatrix N hN 0•τ) := by sorry
