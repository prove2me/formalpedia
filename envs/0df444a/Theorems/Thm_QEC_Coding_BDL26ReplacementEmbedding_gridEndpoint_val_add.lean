-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_gridEndpoint_val_add
-- name    : QEC.Coding.BDL26ReplacementEmbedding.gridEndpoint_val_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:52:12.475845+00:00
-- url     : https://prove2.me/theorems/997712e6-fab6-454e-b36d-f0daa922eca3
-- title:
--   BDL26 Replacement Embedding: grid Endpoint val add
-- statement:
--   The endpoint bit is the actual lower/upper integer increment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2047-L2049
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2047-L2049

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
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.gridEndpoint_val_add {n : Nat} (i : Fin n) (a : BDL26FiniteTannerSquare.Two) :
    (gridEndpoint i a).val = i.val + a.val := by sorry
