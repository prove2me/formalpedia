-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_cusp_phase
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_cusp_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:31:24.690195+00:00
-- url     : https://prove2.me/theorems/9a80c636-c0af-4c56-91b6-31d59abaeadf
-- title:
--   Tanner Lifted Product: lps Original Filled Meromorphic cusp phase
-- statement:
--   Actual cusp representative changes give the SAME filled function a fixed nonzero phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean#L33-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean#L33-L81

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_cusp_phase
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (F : LPSOriginalFilledCurve N → ℂ) :
    letI := lpsOriginalFilledTopology N
    let c := lpsOriginalCuspOrbit N ρ
    let r := lpsOriginalCuspRepresentative N c
    let w := (lpsOriginalCuspGroup N r).strictWidthInfty
    ∃ α : ℂ, α ≠ 0 ∧ ∀ σ : {τ : ℍ // 1 < τ.im},
      F (Sum.inl (lpsOriginalCuspProjection N ρ σ)) =
        F ((lpsOriginalFilledCuspChart N c).symm
          (α * Function.Periodic.qParam w (σ.val : ℂ))) := by sorry
