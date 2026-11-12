-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_xq_transpose_sum_transport
-- name    : QEC.Coding.BDL26NativePresentationGenerator.xq_transpose_sum_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:46:55.178773+00:00
-- url     : https://prove2.me/theorems/7c04547c-7e2f-45bf-a3f1-98324a1c1e6d
-- title:
--   BDL26 Native Presentation Generator: xq transpose sum transport
-- statement:
--   Transposed full-word action uses the same labels, hence both coboundaries transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3206-L3216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3206-L3216

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

theorem QEC.Coding.BDL26NativePresentationGenerator.xq_transpose_sum_transport (S : OddScale) (n : ℕ)
    (w : (state S n).presentation.X → BDL26FiniteTannerSquare.Field) (q : (state S n).presentation.Q) :
    (∑x : Fin (generateQ S n).1.nx,
      nativeXQ (generateQ S n).1 x ((generatedRefines S n).qIndex q) *
        w ((generatedRefines S n).xIndex.symm x))=
      ∑x : (state S n).presentation.X,xqIncidenceMatrix (state S n).presentation x q*w x := by sorry
