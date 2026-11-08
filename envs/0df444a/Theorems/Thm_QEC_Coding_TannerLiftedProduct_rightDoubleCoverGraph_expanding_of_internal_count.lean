-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_expanding_of_internal_count
-- name    : QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_expanding_of_internal_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:14:46.371876+00:00
-- url     : https://prove2.me/theorems/5cf7e9d4-093a-4f74-bb10-f10ef980ffaa
-- title:
--   Tanner Lifted Product: right Double Cover Graph expanding of internal count
-- statement:
--   An induced-edge estimate for small vertex sets implies the two-set mixing
--   bound consumed by the PK22 Tanner proof.  For a `|W|`-regular double cover the
--   resulting constant is `sqrt (2 c |W|)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L527-L541
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L527-L541

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

theorem QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_expanding_of_internal_count
    (label : W → G) (radius : Nat) (internalConstant : ℝ)
    (hInternalNonnegative : 0 ≤ internalConstant)
    (hInternal : ∀ U : Finset (Fin 2 × G), U.card ≤ 2 * radius →
      (SmallSetExpansion.crossCount
        (rightDoubleCoverGraph label) U U : ℝ) ≤
          internalConstant * U.card) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius
      (Real.sqrt (2 * internalConstant * Fintype.card W)) := by sorry
