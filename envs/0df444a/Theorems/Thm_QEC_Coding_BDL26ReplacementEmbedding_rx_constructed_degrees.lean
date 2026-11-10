-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rx_constructed_degrees
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rx_constructed_degrees
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:43:57.858957+00:00
-- url     : https://prove2.me/theorems/42df74c9-934d-4fa6-bcf9-352ed1b0dc17
-- title:
--   BDL26 Replacement Embedding: rx constructed degrees
-- statement:
--   Both measured successor degree bounds accompany RX geometry on its actual presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3564-L3572
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3564-L3572

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
open BDL26BoundedValence

theorem QEC.Coding.BDL26ReplacementEmbedding.rx_constructed_degrees (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (h : BoundedValence P) :
    BoundedValence (rxReplacementPresentation P S) ∧
      (∀ e : XQEdge (rxReplacementPresentation P S),
        Fintype.card (XQIncidentFace (rxReplacementPresentation P S) e) ≤ 4) ∧
      (∀ e : QZEdge (rxReplacementPresentation P S),
        Fintype.card (QZIncidentFace (rxReplacementPresentation P S) e) ≤ 4) := by sorry
