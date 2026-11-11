-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_card_le_hit_labels_mul_fiber
-- name    : QEC.Coding.BDL26ReplacementEmbedding.card_le_hit_labels_mul_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:40:40.945721+00:00
-- url     : https://prove2.me/theorems/9408af2c-9019-4eab-a7b8-de7b1e522c3f
-- title:
--   BDL26 Replacement Embedding: card le hit labels mul fiber
-- statement:
--   Sum a derived geometric estimate only over incoming labels actually hit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2695-L2711
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2695-L2711

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds

theorem QEC.Coding.BDL26ReplacementEmbedding.card_le_hit_labels_mul_fiber {A B : Type*} [DecidableEq B] (s : Finset A) (target : Finset B)
    (owner : A → B) (C : ℝ) (hC : 0 ≤ C)
    (howner : ∀ a ∈ s, owner a ∈ target)
    (hfiber : ∀ b ∈ s.image owner, ((s.filter (fun a => owner a = b)).card : ℝ) ≤ C) :
    (s.card : ℝ) ≤ (target.card : ℝ) * C := by sorry
