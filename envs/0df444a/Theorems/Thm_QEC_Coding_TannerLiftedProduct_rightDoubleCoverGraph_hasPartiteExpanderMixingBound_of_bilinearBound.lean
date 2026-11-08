-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
-- name    : QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:14:43.618573+00:00
-- url     : https://prove2.me/theorems/1c58f63b-d10f-43b9-859f-78f755dca2c3
-- title:
--   Tanner Lifted Product: right Double Cover Graph has Partite Expander Mixing Bound of bilinear Bound
-- statement:
--   A two-sided nontrivial spectral bound on the non-bipartite Cayley graph
--   implies the source's part-normalized mixing estimate on its double cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L425-L437
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L425-L437

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

theorem QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
    (label : W → G) (spectral : ℝ)
    (hSymmetric : SmallSetExpansion.IsSymmetric (rightCayleyGraph label))
    (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : SmallSetExpansion.HasMeanZeroBilinearBound
      (rightCayleyGraph label) spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph label) (Fintype.card W) spectral := by sorry
