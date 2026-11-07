-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_exists_holomorphic_pole_clearing
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_holomorphic_pole_clearing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:29:50.718198+00:00
-- url     : https://prove2.me/theorems/1c195ae6-4c20-4456-9590-c5f6b9161072
-- title:
--   Tanner Lifted Product: lps Original Filled Meromorphic exists holomorphic pole clearing
-- statement:
--   The actual monic pole-clearing polynomial makes P(j)F holomorphic upstairs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L187-L217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L187-L217

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_holomorphic_pole_clearing
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    ∃ P : Polynomial ℂ, P.Monic ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ =>
        P.eval (lpsOriginalJInvariant τ) * F (Sum.inl (Quotient.mk
          (MulAction.orbitRel
            (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ))) := by sorry
