-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_qToZDoubleCylinderEdge_eq_raw
-- name    : QEC.Coding.BDL26ReplacementEmbedding.qToZDoubleCylinderEdge_eq_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:32:49.435611+00:00
-- url     : https://prove2.me/theorems/934a0db7-730f-49fa-b626-2b30687f0df9
-- title:
--   BDL26 Replacement Embedding: q To ZDouble Cylinder Edge eq raw
-- statement:
--   The actual Q-to-Z edge map preserves the same explicit edge in the transpose.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1142-L1147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1142-L1147

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
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.qToZDoubleCylinderEdge_eq_raw (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    qToZDoubleCylinderEdge P A q z hqz S edge =
      qToXDoubleCylinderEdgeRaw (transposePresentation P) q z hqz S edge := by sorry
