-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_labelledSet_eq_empty_of_degree_dichotomy
-- name    : QEC.Coding.TannerLiftedProduct.labelledSet_eq_empty_of_degree_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:40:25.330194+00:00
-- url     : https://prove2.me/theorems/e1e50eea-4a60-4d55-b3d0-7d4790246531
-- title:
--   Tanner Lifted Product: labelled Set eq empty of degree dichotomy
-- statement:
--   A pointwise edge-or-face degree dichotomy and the two small-set mixing
--   bounds force the entire labelled set to be empty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L361-L398
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L361-L398

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype G] [DecidableEq W]

theorem QEC.Coding.TannerLiftedProduct.labelledSet_eq_empty_of_degree_dichotomy
    (label : W → G) (L : Finset (VertexIndex G))
    (radiusEdge radiusFace m s : Nat) (lambdaEdge lambdaFace : ℝ)
    (hLambdaEdge : 0 < lambdaEdge) (hLambdaFace : 0 < lambdaFace)
    (hExpandEdge : SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radiusEdge lambdaEdge)
    (hExpandFace : SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radiusFace lambdaFace)
    (hLRadiusEdge : L.card ≤ radiusEdge)
    (hLRadiusFace : L.card ≤ radiusFace)
    (hDichotomy : ∀ v ∈ L,
      m ≤ ∑ u ∈ L, adjacencyGraph label v u ∨
        s ≤ ∑ u ∈ L, faceSquareGraph label v u)
    (hThresholdEdge : 2 * lambdaEdge ≤ m)
    (hThresholdFace : 2 * lambdaFace ≤ s) :
    L = ∅ := by sorry
