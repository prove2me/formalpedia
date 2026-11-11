-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_qz_sum_transport
-- name    : QEC.Coding.BDL26NativePresentationGenerator.qz_sum_transport
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:47:46.078839+00:00
-- url     : https://prove2.me/theorems/c22d85c3-fe6e-4eaa-a49f-25ccbe7858d2
-- title:
--   BDL26 Native Presentation Generator: qz sum transport
-- statement:
--   The second boundary matrix obeys the same complete reindexing law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3193-L3203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3193-L3203

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

theorem QEC.Coding.BDL26NativePresentationGenerator.qz_sum_transport (S : OddScale) (n : ℕ)
    (w : (state S n).presentation.Z → BDL26FiniteTannerSquare.Field) (q : (state S n).presentation.Q) :
    (∑z : Fin (generateQ S n).1.nz,
      nativeQZ (generateQ S n).1 ((generatedRefines S n).qIndex q) z *
        w ((generatedRefines S n).zIndex.symm z))=
      ∑z : (state S n).presentation.Z,qzIncidenceMatrix (state S n).presentation q z*w z := by sorry
