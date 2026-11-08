-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_eq_sum_sideSlices
-- name    : QEC.Coding.TannerLiftedProduct.sum_eq_sum_sideSlices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:04:56.487796+00:00
-- url     : https://prove2.me/theorems/77e1ff46-076f-4b72-8e8d-1811a5e0b11f
-- title:
--   Tanner Lifted Product: sum eq sum side Slices
-- statement:
--   The Tanner Lifted Product construction uses the sum eq sum side Slices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L307-L321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L307-L321

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

theorem QEC.Coding.TannerLiftedProduct.sum_eq_sum_sideSlices (S : Finset (Fin 2 × G))
    (f : Fin 2 × G → Nat) :
    (∑ x ∈ S, f x) =
      (∑ g ∈ sideSlice S 0, f (0, g)) +
        ∑ g ∈ sideSlice S 1, f (1, g) := by sorry
