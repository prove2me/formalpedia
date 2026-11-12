-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_xq_sum_transport
-- name    : QEC.Coding.BDL26NativePresentationGenerator.xq_sum_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:48:07.277234+00:00
-- url     : https://prove2.me/theorems/3239c32d-cf14-4537-92e2-99132e419cd7
-- title:
--   BDL26 Native Presentation Generator: xq sum transport
-- statement:
--   Arbitrary full input words, not only basis tests, commute with the native XQ matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3180-L3190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3180-L3190

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

theorem QEC.Coding.BDL26NativePresentationGenerator.xq_sum_transport (S : OddScale) (n : ℕ)
    (w : (state S n).presentation.Q → BDL26FiniteTannerSquare.Field) (x : (state S n).presentation.X) :
    (∑q : Fin (generateQ S n).1.nq,
      nativeXQ (generateQ S n).1 ((generatedRefines S n).xIndex x) q *
        w ((generatedRefines S n).qIndex.symm q))=
      ∑q : (state S n).presentation.Q,xqIncidenceMatrix (state S n).presentation x q*w q := by sorry
