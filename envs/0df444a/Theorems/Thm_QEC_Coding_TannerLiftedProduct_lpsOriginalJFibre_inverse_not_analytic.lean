-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFibre_inverse_not_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJFibre_inverse_not_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:09:23.929197+00:00
-- url     : https://prove2.me/theorems/809c3384-3503-4c2f-a6f9-9b7cfc45250e
-- title:
--   Tanner Lifted Product: lps Original JFibre inverse not analytic
-- statement:
--   The Tanner Lifted Product construction uses the lps Original JFibre inverse not analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFiniteInteriorFibres.lean#L90-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFiniteInteriorFibres.lean#L90-L129

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
include hpos

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJFibre_inverse_not_analytic (a : ℂ) (y : Q)
    (hy : lpsOriginalFilledJ N (Sum.inl y) = a) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ¬ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ((lpsOriginalFilledJ N - fun _ => a)⁻¹) (Sum.inl y) := by sorry
