-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFace_card_eq_flatCell
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rxFace_card_eq_flatCell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:50:03.346706+00:00
-- url     : https://prove2.me/theorems/2859b1ff-b8d5-4a03-b607-9035d2546146
-- title:
--   BDL26 Replacement Embedding: rx Face card eq flat Cell
-- statement:
--   Actual RX and the explicit flat patch have the same exact face multiplicity.
--   This cardinal equality does not identify their geometric realizations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L66-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L66-L78

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rxFace_card_eq_flatCell (P : TannerSquarePresentation) (S : OddScale) :
    Fintype.card (RXFace P S) = Fintype.card P.Face * Fintype.card (FlatCell S) := by sorry
