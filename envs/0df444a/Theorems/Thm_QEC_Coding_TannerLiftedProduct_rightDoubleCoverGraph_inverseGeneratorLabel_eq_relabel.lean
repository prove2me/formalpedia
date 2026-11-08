-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_inverseGeneratorLabel_eq_relabel
-- name    : QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_inverseGeneratorLabel_eq_relabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:42:52.075594+00:00
-- url     : https://prove2.me/theorems/d9ea66db-9b7a-4ed3-8e5e-9e25703bc099
-- title:
--   Tanner Lifted Product: right Double Cover Graph inverse Generator Label eq relabel
-- statement:
--   The Tanner Lifted Product construction uses the right Double Cover Graph inverse Generator Label eq relabel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L959-L977
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L959-L977

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_relabel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq W] [Fintype R] [DecidableEq R] [Fintype R']
    [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_inverseGeneratorLabel_eq_relabel
    (label : W → G) :
    rightDoubleCoverGraph (inverseGeneratorLabel label) =
      SmallSetExpansion.relabel doubleCoverSideSwapEquiv
        (rightDoubleCoverGraph label) := by sorry
