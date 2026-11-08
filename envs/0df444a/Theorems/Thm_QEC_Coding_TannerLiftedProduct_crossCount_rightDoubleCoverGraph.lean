-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_crossCount_rightDoubleCoverGraph
-- name    : QEC.Coding.TannerLiftedProduct.crossCount_rightDoubleCoverGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:06:06.842106+00:00
-- url     : https://prove2.me/theorems/af11fe89-e510-4df3-ac09-4dedf78c1399
-- title:
--   Tanner Lifted Product: cross Count right Double Cover Graph
-- statement:
--   Cross counts in a labelled double cover are the two opposite-side cross
--   counts of its underlying Cayley multigraph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L326-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L326-L338

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [DecidableEq W]

theorem QEC.Coding.TannerLiftedProduct.crossCount_rightDoubleCoverGraph
    (label : W → G) (S T : Finset (Fin 2 × G)) :
    SmallSetExpansion.crossCount (rightDoubleCoverGraph label) S T =
      SmallSetExpansion.crossCount (rightCayleyGraph label)
          (sideSlice S 0) (sideSlice T 1) +
        SmallSetExpansion.crossCount (rightCayleyGraph label)
          (sideSlice T 0) (sideSlice S 1) := by sorry
