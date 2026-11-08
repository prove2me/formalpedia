-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalGraph_eq_relabel_disjointUnion
-- name    : QEC.Coding.TannerLiftedProduct.verticalGraph_eq_relabel_disjointUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:05:32.024934+00:00
-- url     : https://prove2.me/theorems/85601764-6fac-493f-aa1f-3ba37e32f3e9
-- title:
--   Tanner Lifted Product: vertical Graph eq relabel disjoint Union
-- statement:
--   Vertical product adjacency is a disjoint union of left double covers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L570-L591
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L570-L591

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

theorem QEC.Coding.TannerLiftedProduct.verticalGraph_eq_relabel_disjointUnion (label : W → G) :
    verticalGraph label =
      SmallSetExpansion.relabel verticalFiberEquiv
        (SmallSetExpansion.disjointUnion
          (fun _ : Fin 2 => leftDoubleCoverGraph label)) := by sorry
