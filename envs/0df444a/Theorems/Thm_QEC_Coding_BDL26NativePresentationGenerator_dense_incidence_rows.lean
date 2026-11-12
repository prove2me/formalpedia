-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_dense_incidence_rows
-- name    : QEC.Coding.BDL26NativePresentationGenerator.dense_incidence_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:51:28.778203+00:00
-- url     : https://prove2.me/theorems/1ee391e4-ce9c-44b4-bb8c-dfd4a472b3d7
-- title:
--   BDL26 Native Presentation Generator: dense incidence rows
-- statement:
--   Every true and false dense coefficient is present, with both original indices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3261-L3274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3261-L3274

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation

theorem QEC.Coding.BDL26NativePresentationGenerator.dense_incidence_rows (S : OddScale) (n : ℕ)
    (x : (state S n).presentation.X) (q : (state S n).presentation.Q)
    (z : (state S n).presentation.Z) :
    (((generatedRefines S n).xIndex x).val,((generatedRefines S n).qIndex q).val,
      (state S n).presentation.xq x q)∈(runQ S n).1.xq ∧
    (((generatedRefines S n).qIndex q).val,((generatedRefines S n).zIndex z).val,
      (state S n).presentation.qz q z)∈(runQ S n).1.qz := by sorry
