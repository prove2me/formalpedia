-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJ_jN_monic_relation
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJ_jN_monic_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:54:40.805902+00:00
-- url     : https://prove2.me/theorems/6740926a-7996-425f-9b2b-e03038d63175
-- title:
--   Tanner Lifted Product: lps Original J j N monic relation
-- statement:
--   Explicitly normalized original j/jN relation is MONIC and has EXACT actual finite coset degree for every positive level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L331-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L331-L358

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJ_jN_monic_relation (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ Φ : Polynomial (Polynomial ℂ), Φ.Monic ∧
      Φ.natDegree=Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧ ∀ τ : ℍ,
      Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
        (lpsOriginalJDilated N hN τ)=0 := by sorry
