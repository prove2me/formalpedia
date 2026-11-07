-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_factorMatrix
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_factorMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:13:17.39388+00:00
-- url     : https://prove2.me/theorems/4a46583a-7a13-45d5-8391-77f998d06c87
-- title:
--   Tanner Lifted Product: lps Hecke Conjugate Intersection factor Matrix
-- statement:
--   The zero finite representative has a genuine integral factor for every second-intersection matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L105-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L105-L129

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_factorMatrix (N p : ℕ) [Fact p.Prime]
    (γ : SL(2,ℤ)) (hγ : γ ∈ lpsHeckeConjugateIntersection N p) :
    ∃δ : SL(2,ℤ),δ ∈ CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p (some ⟨0,(Fact.out:p.Prime).pos⟩) *
          (γ:Matrix (Fin 2) (Fin 2) ℤ) =
        (δ:Matrix (Fin 2) (Fin 2) ℤ) *
          lpsHeckeUpperMatrix p (some ⟨0,(Fact.out:p.Prime).pos⟩) := by sorry
