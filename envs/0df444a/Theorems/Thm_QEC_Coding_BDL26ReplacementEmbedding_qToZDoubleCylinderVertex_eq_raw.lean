-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_qToZDoubleCylinderVertex_eq_raw
-- name    : QEC.Coding.BDL26ReplacementEmbedding.qToZDoubleCylinderVertex_eq_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:33:02.869653+00:00
-- url     : https://prove2.me/theorems/deb60117-9a18-4a41-8602-9e02eab05043
-- title:
--   BDL26 Replacement Embedding: q To ZDouble Cylinder Vertex eq raw
-- statement:
--   Every Q-to-Z vertex tag agrees with the same-edge transpose construction;
--   the chosen cone-point root affects no materialized vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1133-L1139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1133-L1139

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

theorem QEC.Coding.BDL26ReplacementEmbedding.qToZDoubleCylinderVertex_eq_raw (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (root : QStarEdge (transposePresentation P) q)
    (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    qToZDoubleCylinderVertex P A q z hqz S v =
      qToXDoubleCylinderVertexAtRoot (transposePresentation P) q z hqz S root v := by sorry
