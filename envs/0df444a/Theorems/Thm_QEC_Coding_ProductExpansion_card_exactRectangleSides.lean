-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_exactRectangleSides
-- name    : QEC.Coding.ProductExpansion.card_exactRectangleSides
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:22.252539+00:00
-- url     : https://prove2.me/theorems/a51398bc-d293-49c4-ac1b-03518a9838c5
-- title:
--   Product Expansion: card exact Rectangle Sides
-- statement:
--   Number of exact rectangle sides.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1089-L1094
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1089-L1094

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.card_exactRectangleSides (W : Type v) [Fintype W] (m : Nat) :
    Nat.card (exactRectangleSides W m) =
      Nat.choose (Fintype.card W) (Fintype.card W - m) := by sorry
