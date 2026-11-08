-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_expanding_of_bilinearBound
-- name    : QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_expanding_of_bilinearBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:14:49.40457+00:00
-- url     : https://prove2.me/theorems/4bda6ec7-44cf-4d17-b084-3281f0ad622e
-- title:
--   Tanner Lifted Product: right Double Cover Graph expanding of bilinear Bound
-- statement:
--   An abstract full mean-zero bilinear bound on the labelled double cover
--   implies small-set expansion, with the density term explicit. A nonempty
--   bipartite double cover has a trivial side-sign eigenmode, so a subdegree
--   full mean-zero bound cannot serve as PK22's spectral input; use the
--   part-normalized mixing bridge above for that application.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L508-L521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L508-L521

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

theorem QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_expanding_of_bilinearBound
    (label : W → G) (radius : Nat) (spectral density : ℝ)
    (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : SmallSetExpansion.HasMeanZeroBilinearBound
      (rightDoubleCoverGraph label) spectral)
    (hDensity : (Fintype.card W : ℝ) * radius ≤
      density * Fintype.card (Fin 2 × G)) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius (spectral + density) := by sorry
