-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_cellular_transport
-- name    : QEC.Coding.BDL26NativePresentationGenerator.cellular_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:50:42.803046+00:00
-- url     : https://prove2.me/theorems/24d8e103-f5f2-4e20-a779-c5da4cd2f2aa
-- title:
--   BDL26 Native Presentation Generator: cellular transport
-- statement:
--   Both cellular boundaries and both coboundaries commute with the constructed
--   bijections for arbitrary full words.  The last two equations are the transposes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3506-L3552
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3506-L3552

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation

theorem QEC.Coding.BDL26NativePresentationGenerator.cellular_transport (S : OddScale) (n : ℕ)
    (a : Edge (state S n).presentation → BDL26FiniteTannerSquare.Field)
    (b : (state S n).presentation.Face → BDL26FiniteTannerSquare.Field)
    (c : Vertex (state S n).presentation → BDL26FiniteTannerSquare.Field)
    (d : Edge (state S n).presentation → BDL26FiniteTannerSquare.Field) :
    (∀v, (∑e,nativeBoundary1 (generateQ S n).1 (generatedVertexIndex S n v) e *
        a ((generatedEdgeIndex S n).symm e))=
      ∑e,edgeVertexMatrix (state S n).presentation v e*a e) ∧
    (∀e, (∑f,nativeBoundary2 (generateQ S n).1 (generatedEdgeIndex S n e) f *
        b ((generatedRefines S n).fIndex.symm f))=
      ∑f,faceEdgeMatrix (state S n).presentation e f*b f) ∧
    (∀e, (∑v,nativeBoundary1 (generateQ S n).1 v (generatedEdgeIndex S n e) *
        c ((generatedVertexIndex S n).symm v))=
      ∑v,edgeVertexMatrix (state S n).presentation v e*c v) ∧
    (∀f, (∑e,nativeBoundary2 (generateQ S n).1 e ((generatedRefines S n).fIndex f) *
        d ((generatedEdgeIndex S n).symm e))=
      ∑e,faceEdgeMatrix (state S n).presentation e f*d e) := by sorry
