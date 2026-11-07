-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJ_jN_integer_monic_relation
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJ_jN_integer_monic_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:16:57.292208+00:00
-- url     : https://prove2.me/theorems/cbd77730-e01a-481e-8ad2-f592fbcd1cde
-- title:
--   Tanner Lifted Product: lps Original J j N integer monic relation
-- statement:
--   The complete original integer monic modular equation, at exact coset degree, for every positive composite or prime level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L927-L978
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L927-L978

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJ_jN_integer_monic_relation
    (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ Ψ : Polynomial (Polynomial ℤ), Ψ.Monic ∧
      Ψ.natDegree=Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, Ψ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) (lpsOriginalJDilated N hN τ)=0 := by sorry
