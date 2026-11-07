-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_finrank_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_finrank_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:06:05.735634+00:00
-- url     : https://prove2.me/theorems/1beda984-a5e2-4506-8a1e-978a6a6e1f84
-- title:
--   Tanner Lifted Product: lps Original Generated Function Field Q finrank eq
-- statement:
--   The exact degree of SAME generated original Q(j,jN) equals actual Gamma0 coset cardinal, using the SAME genuine distinct branches.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L266-L300
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L266-L300

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_finrank_eq (N : ℕ) [NeZero N]
    (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Module.finrank (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)=
      Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by sorry
