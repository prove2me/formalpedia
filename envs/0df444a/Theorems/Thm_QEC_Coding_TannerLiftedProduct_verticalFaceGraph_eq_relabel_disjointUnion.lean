-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalFaceGraph_eq_relabel_disjointUnion
-- name    : QEC.Coding.TannerLiftedProduct.verticalFaceGraph_eq_relabel_disjointUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:05:42.907053+00:00
-- url     : https://prove2.me/theorems/19752609-4271-4039-871a-d1e821cc16a9
-- title:
--   Tanner Lifted Product: vertical Face Graph eq relabel disjoint Union
-- statement:
--   The physical vertical-edge face graph is a disjoint union, indexed by the
--   vertical local direction, of right double covers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L651-L675
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L651-L675

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_disjointUnion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_relabel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G]

theorem QEC.Coding.TannerLiftedProduct.verticalFaceGraph_eq_relabel_disjointUnion (label : W → G) :
    verticalFaceGraph label =
      SmallSetExpansion.relabel verticalEdgeFiberEquiv
        (SmallSetExpansion.disjointUnion
          (fun _ : W => rightDoubleCoverGraph label)) := by sorry
