-- Prove2me | Theorems.Thm_QEC_Bounds_BPT_EmbeddedInteractionFamily_interactionsAtLengthAtLeast_eq_card
-- name    : QEC.Bounds.BPT.EmbeddedInteractionFamily.interactionsAtLengthAtLeast_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:08:27.101464+00:00
-- url     : https://prove2.me/theorems/31dfb1eb-beba-4654-85d7-8efb491683c0
-- title:
--   Embedded Interaction Family: interactions At Length At Least eq card
-- statement:
--   The family accessor unfolds to the cardinality of the actual unordered edge set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean#L337-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean#L337-L342

import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Bound
set_option autoImplicit false
open QEC
universe u v w
open QEC.Bounds
open QEC.Bounds.BPT
open QEC.Bounds.BPT.EmbeddedInteractionFamily

theorem QEC.Bounds.BPT.EmbeddedInteractionFamily.interactionsAtLengthAtLeast_eq_card {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (data : EmbeddedInteractionFamily ι κ) (i : Nat) (threshold : ℝ) :
    data.interactionsAtLengthAtLeast i threshold =
      ((data.presentation i).interactionsAtLengthAtLeast (data.embedding i) threshold).card := by sorry
