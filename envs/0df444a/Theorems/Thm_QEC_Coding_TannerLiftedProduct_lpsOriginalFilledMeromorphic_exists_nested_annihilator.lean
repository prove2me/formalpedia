-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_exists_nested_annihilator
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_nested_annihilator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:38:13.830615+00:00
-- url     : https://prove2.me/theorems/79024967-8312-4847-9e35-0734fd0a7316
-- title:
--   Tanner Lifted Product: lps Original Filled Meromorphic exists nested annihilator
-- statement:
--   Every actual filled-curve meromorphic function has a nonzero original j equation of bounded degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L238-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L238-L250

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_nested_annihilator
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    ∃ Φ : Polynomial (Polynomial ℂ), Φ ≠ 0 ∧
      Φ.natDegree ≤ Nat.card (LPSOriginalMeromorphicCosets N) ∧ ∀ τ : ℍ,
      Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
        (F (Sum.inl ⟦τ⟧)) = 0 := by sorry
