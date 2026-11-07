-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFullMeromorphic_bounded_annihilator
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFullMeromorphic_bounded_annihilator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:38:51.628093+00:00
-- url     : https://prove2.me/theorems/1ae48cbe-6872-4b67-9f5a-3577e7b32fd5
-- title:
--   Tanner Lifted Product: lps Original Full Meromorphic bounded annihilator
-- statement:
--   Every element of the entire actual restriction field has a monic bounded-degree C(j) annihilator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L343-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L343-L373

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFullMeromorphic_bounded_annihilator
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
    ∀ x : lpsOriginalFilledMeromorphicRestrictionSubfield N hN,
      ∃ P : Polynomial (FractionRing (Polynomial ℂ)), P.Monic ∧
        P.natDegree ≤ Nat.card (LPSOriginalMeromorphicCosets N) ∧ Polynomial.aeval x P = 0 := by sorry
