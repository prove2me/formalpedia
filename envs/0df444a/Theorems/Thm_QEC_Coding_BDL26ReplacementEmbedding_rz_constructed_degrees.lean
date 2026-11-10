-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rz_constructed_degrees
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rz_constructed_degrees
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:44:23.731458+00:00
-- url     : https://prove2.me/theorems/ce454e73-fa82-477f-8d3c-67628e70acf1
-- title:
--   BDL26 Replacement Embedding: rz constructed degrees
-- statement:
--   The RZ degree conclusion uses the actual constructed dual successor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3575-L3582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3575-L3582

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rz_constructed_degrees (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (h : BoundedValence P) :
    let P' := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
    BoundedValence P' ∧
      (∀ e : XQEdge P', Fintype.card (XQIncidentFace P' e) ≤ 4) ∧
      (∀ e : QZEdge P', Fintype.card (QZIncidentFace P' e) ≤ 4) := by sorry
