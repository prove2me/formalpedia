-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedNorm_delta_scalar
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_delta_scalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:01:17.042213+00:00
-- url     : https://prove2.me/theorems/3745ec29-138b-47bb-b182-43f4b7dd8332
-- title:
--   Tanner Lifted Product: lps Original Delta Dilated Norm delta scalar
-- statement:
--   For every positive level the genuine original Delta norm equals nonzero scalar times Delta^r.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L258-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L258-L264

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_delta_scalar (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ c : ℂ, c≠0 ∧ ∀ τ : ℍ, lpsOriginalDeltaDilatedNorm N hN τ=
      c*ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)) := by sorry
