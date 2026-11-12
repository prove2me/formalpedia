-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_qz_transpose_sum_transport
-- name    : QEC.Coding.BDL26NativePresentationGenerator.qz_transpose_sum_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:47:33.033266+00:00
-- url     : https://prove2.me/theorems/e5c5f6d3-e0d8-4cb2-aefd-c0314da45560
-- title:
--   BDL26 Native Presentation Generator: qz transpose sum transport
-- statement:
--   The BDL26 Native Presentation Generator construction uses the qz transpose sum transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3218-L3228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3218-L3228

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

theorem QEC.Coding.BDL26NativePresentationGenerator.qz_transpose_sum_transport (S : OddScale) (n : ℕ)
    (w : (state S n).presentation.Q → BDL26FiniteTannerSquare.Field) (z : (state S n).presentation.Z) :
    (∑q : Fin (generateQ S n).1.nq,
      nativeQZ (generateQ S n).1 q ((generatedRefines S n).zIndex z) *
        w ((generatedRefines S n).qIndex.symm q))=
      ∑q : (state S n).presentation.Q,qzIncidenceMatrix (state S n).presentation q z*w q := by sorry
