-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_rx_step_cost
-- name    : QEC.Coding.BDL26NativePresentationGenerator.rx_step_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:02:52.322337+00:00
-- url     : https://prove2.me/theorems/a805bb9a-ca8a-4ddd-ac5e-0d7cce0561b1
-- title:
--   BDL26 Native Presentation Generator: rx step cost
-- statement:
--   All raw candidates, rejected descriptors, dedup scans and four handle scans
--   are bounded before any actual-state cardinality theorem enters.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L4382-L4464
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L4382-L4464

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

theorem QEC.Coding.BDL26NativePresentationGenerator.rx_step_cost (F : Frame) (m : ℕ) :
    (rxFrameQ F m).2≤(radius F m)^190 ∧ frameSize (rxFrameQ F m).1≤(radius F m)^88 := by sorry
