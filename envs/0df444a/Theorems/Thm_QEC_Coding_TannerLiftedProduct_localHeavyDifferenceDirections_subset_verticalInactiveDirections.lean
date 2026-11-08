-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localHeavyDifferenceDirections_subset_verticalInactiveDirections
-- name    : QEC.Coding.TannerLiftedProduct.localHeavyDifferenceDirections_subset_verticalInactiveDirections
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:38:28.811657+00:00
-- url     : https://prove2.me/theorems/85ec6246-b435-46e5-b908-40f3bc9ee6a8
-- title:
--   Tanner Lifted Product: local Heavy Difference Directions subset vertical Inactive Directions
-- statement:
--   The Tanner Lifted Product construction uses the local Heavy Difference Directions subset vertical Inactive Directions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L763-L771
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L763-L771

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [Fintype G] [DecidableEq G]
    [DecidableEq W] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.localHeavyDifferenceDirections_subset_verticalInactiveDirections
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    localHeavyDifferenceDirections label h hRank h' c v ⊆
      verticalInactiveDirections label c v := by sorry
