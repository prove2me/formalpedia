-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_fineEndpointBit_eq_of_coordinate_eq
-- name    : QEC.Coding.BDL26ReplacementEmbedding.fineEndpointBit_eq_of_coordinate_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:39:03.779255+00:00
-- url     : https://prove2.me/theorems/26c50539-c584-4c03-8b64-450d5562f42c
-- title:
--   BDL26 Replacement Embedding: fine Endpoint Bit eq of coordinate eq
-- statement:
--   Equal actual fine coordinates have equal endpoint bits, including the last strip.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2339-L2345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2339-L2345

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

theorem QEC.Coding.BDL26ReplacementEmbedding.fineEndpointBit_eq_of_coordinate_eq (S : OddScale) (i j : FineCoordinate S)
    (h : ((fineCoordinateEquiv S i).val : ℤ) = ((fineCoordinateEquiv S j).val : ℤ)) :
    fineEndpointBit S i = fineEndpointBit S j := by sorry
