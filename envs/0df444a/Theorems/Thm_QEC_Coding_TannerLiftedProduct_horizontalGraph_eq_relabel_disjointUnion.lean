-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalGraph_eq_relabel_disjointUnion
-- name    : QEC.Coding.TannerLiftedProduct.horizontalGraph_eq_relabel_disjointUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:05:24.863987+00:00
-- url     : https://prove2.me/theorems/d8cb50d0-22ab-41d0-90b6-2a554ea6b1ff
-- title:
--   Tanner Lifted Product: horizontal Graph eq relabel disjoint Union
-- statement:
--   Horizontal product adjacency is a disjoint union of right double covers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L545-L566
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L545-L566

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
omit [Fintype G] [DecidableEq W]

theorem QEC.Coding.TannerLiftedProduct.horizontalGraph_eq_relabel_disjointUnion (label : W → G) :
    horizontalGraph label =
      SmallSetExpansion.relabel horizontalFiberEquiv
        (SmallSetExpansion.disjointUnion
          (fun _ : Fin 2 => rightDoubleCoverGraph label)) := by sorry
