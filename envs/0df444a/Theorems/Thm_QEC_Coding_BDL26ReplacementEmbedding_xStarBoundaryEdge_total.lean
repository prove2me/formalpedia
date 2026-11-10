-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_xStarBoundaryEdge_total
-- name    : QEC.Coding.BDL26ReplacementEmbedding.xStarBoundaryEdge_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:27:00.002023+00:00
-- url     : https://prove2.me/theorems/be457aed-ba56-487e-882a-a3213cd75fc5
-- title:
--   BDL26 Replacement Embedding: x Star Boundary Edge total
-- statement:
--   Boundary incidences have exactly two labels per old face.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L48-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L48-L52

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

theorem QEC.Coding.BDL26ReplacementEmbedding.xStarBoundaryEdge_total (P : TannerSquarePresentation) :
    (∑ x : P.X, Fintype.card (XStarBoundaryEdge P x)) = 2 * Fintype.card P.Face := by sorry
