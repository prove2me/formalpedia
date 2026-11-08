-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_complexWeightedNeighborSum_rightCayleyGraph
-- name    : QEC.Coding.TannerLiftedProduct.complexWeightedNeighborSum_rightCayleyGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:12:06.677205+00:00
-- url     : https://prove2.me/theorems/afed7a78-325f-4d29-9af0-392571bfc7f6
-- title:
--   Tanner Lifted Product: complex Weighted Neighbor Sum right Cayley Graph
-- statement:
--   The weighted adjacency operator of the labelled right Cayley multigraph
--   is exactly its right-translation sum, including label multiplicities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L262-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L262-L287

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]

theorem QEC.Coding.TannerLiftedProduct.complexWeightedNeighborSum_rightCayleyGraph
    (label : W → G) (f : G → ℂ) (g : G) :
    SmallSetExpansion.complexWeightedNeighborSum
        (rightCayleyGraph label) f g =
      cayleyRightTranslationSum label f g := by sorry
