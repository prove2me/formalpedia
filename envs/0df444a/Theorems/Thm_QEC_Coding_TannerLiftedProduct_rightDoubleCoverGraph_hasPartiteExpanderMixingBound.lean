-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_hasPartiteExpanderMixingBound
-- name    : QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_hasPartiteExpanderMixingBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:06:06.515697+00:00
-- url     : https://prove2.me/theorems/05b657fa-18b1-4a6b-af6b-9a743ce87a11
-- title:
--   Tanner Lifted Product: right Double Cover Graph has Partite Expander Mixing Bound
-- statement:
--   Expander mixing for the non-bipartite Cayley graph passes to the
--   bipartite double cover without changing the nontrivial spectral constant.
--   The two trivial double-cover modes are represented by the part-normalized
--   density term in `HasPartiteExpanderMixingBound`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L345-L420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L345-L420

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

theorem QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_hasPartiteExpanderMixingBound
    (label : W → G) (degree : Nat) (spectral : ℝ)
    (hSpectralNonnegative : 0 ≤ spectral)
    (hMixing : SmallSetExpansion.HasExpanderMixingBound
      (rightCayleyGraph label) degree spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph label) degree spectral := by sorry
