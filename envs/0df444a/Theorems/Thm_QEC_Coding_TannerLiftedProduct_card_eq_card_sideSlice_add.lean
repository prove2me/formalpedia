-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_eq_card_sideSlice_add
-- name    : QEC.Coding.TannerLiftedProduct.card_eq_card_sideSlice_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:05:00.427928+00:00
-- url     : https://prove2.me/theorems/0c4e69fd-b351-4b71-9da7-6a2af1621284
-- title:
--   Tanner Lifted Product: card eq card side Slice add
-- statement:
--   The Tanner Lifted Product construction uses the card eq card side Slice add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L294-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L294-L304

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Group G]

theorem QEC.Coding.TannerLiftedProduct.card_eq_card_sideSlice_add (S : Finset (Fin 2 × G)) :
    S.card = (sideSlice S 0).card + (sideSlice S 1).card := by sorry
