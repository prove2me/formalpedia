-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_unlabelledActiveVerticalEdges_eq_empty
-- name    : QEC.Coding.TannerLiftedProduct.unlabelledActiveVerticalEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:04:38.602342+00:00
-- url     : https://prove2.me/theorems/2457ee6c-5f47-4617-bb92-16717ef9b3b9
-- title:
--   Tanner Lifted Product: unlabelled Active Vertical Edges eq empty
-- statement:
--   PK22 `lemma:lbl-edge` for the physical vertical-edge graph: every active
--   vertical edge has a labelled endpoint once the first local-code distance and
--   small-set expansion beat the `2m` closure threshold.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L1074-L1095
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L1074-L1095

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

theorem QEC.Coding.TannerLiftedProduct.unlabelledActiveVerticalEdges_eq_empty
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
    (hThreshold : (2 * m : ℝ) + lambda ≤ d) :
    unlabelledActiveVerticalEdges label c L = ∅ := by sorry
