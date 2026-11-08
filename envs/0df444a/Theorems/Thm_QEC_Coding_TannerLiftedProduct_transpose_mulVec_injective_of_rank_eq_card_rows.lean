-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_transpose_mulVec_injective_of_rank_eq_card_rows
-- name    : QEC.Coding.TannerLiftedProduct.transpose_mulVec_injective_of_rank_eq_card_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:44:10.713568+00:00
-- url     : https://prove2.me/theorems/fe2e5017-9357-4474-aaf8-a19f961f412a
-- title:
--   Tanner Lifted Product: transpose mul Vec injective of rank eq card rows
-- statement:
--   Maximal row rank makes the transpose generator map injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean#L30-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean#L30-L44

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_24
omit [Fintype F] [DecidableEq W]

theorem QEC.Coding.TannerLiftedProduct.transpose_mulVec_injective_of_rank_eq_card_rows
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R) :
    Function.Injective (fun u : Word F R => h.transpose.mulVec u) := by sorry
