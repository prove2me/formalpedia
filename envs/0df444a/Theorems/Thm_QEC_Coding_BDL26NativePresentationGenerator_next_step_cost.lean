-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_next_step_cost
-- name    : QEC.Coding.BDL26NativePresentationGenerator.next_step_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:01:50.076863+00:00
-- url     : https://prove2.me/theorems/dda95fd9-6dbe-4771-900c-df1d1ab20352
-- title:
--   BDL26 Native Presentation Generator: next step cost
-- statement:
--   A single actual parity step pays its complete raw construction and transpose scans.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L4477-L4521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L4477-L4521

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

theorem QEC.Coding.BDL26NativePresentationGenerator.next_step_cost (S : OddScale) (n : ℕ) (F : Frame) :
    (nextFrameQ S n F).2≤(radius F S.half)^200 := by sorry
