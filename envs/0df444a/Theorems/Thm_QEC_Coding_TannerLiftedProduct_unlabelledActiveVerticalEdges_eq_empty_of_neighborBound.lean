-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_unlabelledActiveVerticalEdges_eq_empty_of_neighborBound
-- name    : QEC.Coding.TannerLiftedProduct.unlabelledActiveVerticalEdges_eq_empty_of_neighborBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:04:54.97421+00:00
-- url     : https://prove2.me/theorems/6b8654d8-ea92-4204-8848-b75e44914ce1
-- title:
--   Tanner Lifted Product: unlabelled Active Vertical Edges eq empty of neighbor Bound
-- statement:
--   The source labelled-edge argument reduced to its remaining incidence
--   geometry.  The `hNeighborBound` hypothesis is the double-cover fact that
--   active face-neighbours outside `S` choose distinct labelled vertices adjacent
--   to one of the two endpoints of `e`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L1002-L1069
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L1002-L1069

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.unlabelledActiveVerticalEdges_eq_empty_of_neighborBound
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m radius : Nat) (lambda : ℝ)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (L : Finset (VertexIndex G))
    (hClosed : IsClosedLabelledSet label c m L)
    (hExpand : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radius lambda)
    (hActiveRadius : (activeVerticalEdges label c).card ≤ radius)
    (hNeighborBound : ∀ e ∈ unlabelledActiveVerticalEdges label c L,
      (∑ e' ∈ activeVerticalEdges label c \
          unlabelledActiveVerticalEdges label c L,
          verticalFaceGraph label e e') ≤
        (∑ u ∈ L,
          adjacencyGraph label (verticalEdgeEndpoint label e 0) u) +
        ∑ u ∈ L, adjacencyGraph label
          (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) u)
    (hThreshold : (2 * m : ℝ) + lambda ≤ d) :
    unlabelledActiveVerticalEdges label c L = ∅ := by sorry
