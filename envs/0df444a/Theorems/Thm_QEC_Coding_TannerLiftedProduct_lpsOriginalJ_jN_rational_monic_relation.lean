-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJ_jN_rational_monic_relation
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJ_jN_rational_monic_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:57:20.272284+00:00
-- url     : https://prove2.me/theorems/83052cab-972c-481f-8c4f-fbe67e58fc69
-- title:
--   Tanner Lifted Product: lps Original J j N rational monic relation
-- statement:
--   Owned rational MONIC annihilator for SAME original j/jN at every positive level, with genuine finite coset-degree and no supplied relation/model.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L597-L606
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L597-L606

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJ_jN_rational_monic_relation (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ Φ : Polynomial (Polynomial ℚ), Φ.Monic ∧
      Φ.natDegree=Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧ ∀ τ : ℍ,
      Φ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0 := by sorry
