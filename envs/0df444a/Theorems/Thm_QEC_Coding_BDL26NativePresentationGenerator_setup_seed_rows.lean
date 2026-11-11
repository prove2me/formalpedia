-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_setup_seed_rows
-- name    : QEC.Coding.BDL26NativePresentationGenerator.setup_seed_rows
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:53:13.761107+00:00
-- url     : https://prove2.me/theorems/975ccfa0-e817-4c5a-aa0c-727a9288e5af
-- title:
--   BDL26 Native Presentation Generator: setup seed rows
-- statement:
--   Seed allocation is part of the same public setup run and is never zero-cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3620-L3630
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3620-L3630

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

theorem QEC.Coding.BDL26NativePresentationGenerator.setup_seed_rows (S : OddScale) (n : ℕ) :
    (setupQ S n).1.seedRows.length=9 ∧
    (∀r∈(setupQ S n).1.seedRows,r.counter=0 ∧ r.point=(0,0,0)) ∧
    seedRowsQ.2≤(setupQ S n).2 ∧ 168≤(setupQ S n).2 := by sorry
