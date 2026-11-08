-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_HasPartiteExpanderMixingBound_toSmallSetEdgeExpanding
-- name    : QEC.Coding.TannerLiftedProduct.HasPartiteExpanderMixingBound.toSmallSetEdgeExpanding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:01:11.783355+00:00
-- url     : https://prove2.me/theorems/e6284e4d-b521-488a-be38-8de7455130f4
-- title:
--   Has Partite Expander Mixing Bound: to Small Set Edge Expanding
-- statement:
--   A part-normalized bipartite mixing estimate gives the exact PK22
--   small-set bound.  The double cover's second trivial mode is absorbed by the
--   density contribution `degree * radius / |G|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L443-L487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L443-L487

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_HasExpanderMixingBound_toSmallSetEdgeExpanding

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [DecidableEq G]

theorem QEC.Coding.TannerLiftedProduct.HasPartiteExpanderMixingBound.toSmallSetEdgeExpanding
    {M : SmallSetExpansion.WeightedGraph (Fin 2 × G)}
    {degree radius : Nat} {spectral density : ℝ}
    (hMixing : HasPartiteExpanderMixingBound M degree spectral)
    (hDensity : (degree : ℝ) * radius ≤ density * Fintype.card G) :
    SmallSetExpansion.IsSmallSetEdgeExpanding M radius (spectral + density) := by sorry
