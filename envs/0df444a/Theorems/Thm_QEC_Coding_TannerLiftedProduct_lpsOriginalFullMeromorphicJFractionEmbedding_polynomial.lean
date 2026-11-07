-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFullMeromorphicJFractionEmbedding_polynomial
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFullMeromorphicJFractionEmbedding_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:38:31.975554+00:00
-- url     : https://prove2.me/theorems/6b708a7f-acf1-4479-8dc4-251bd03cc6e4
-- title:
--   Tanner Lifted Product: lps Original Full Meromorphic JFraction Embedding polynomial
-- statement:
--   The faithful C(j) map on polynomials recovers literal original j germs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L289-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L289-L301

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFullMeromorphicJFractionEmbedding_polynomial
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (P : Polynomial ℂ) :
    (lpsOriginalFullMeromorphicJFractionEmbedding N hN
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) P)).val.val =
      Filter.Germ.coeRingHom (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet)
        (lpsOriginalMeromorphicJFunctionCoefficient P) := by sorry
