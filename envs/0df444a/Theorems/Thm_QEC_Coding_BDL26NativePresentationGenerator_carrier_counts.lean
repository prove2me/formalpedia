-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_carrier_counts
-- name    : QEC.Coding.BDL26NativePresentationGenerator.carrier_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:42:22.224792+00:00
-- url     : https://prove2.me/theorems/7d6cd48b-ac3b-47b8-bc84-ddb8acf9f092
-- title:
--   BDL26 Native Presentation Generator: carrier counts
-- statement:
--   The four complete generated carrier lengths, all depths and both parities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3102-L3111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3102-L3111

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

theorem QEC.Coding.BDL26NativePresentationGenerator.carrier_counts (S : OddScale) (n : ℕ) :
    (generateQ S n).1.nx=Fintype.card (state S n).presentation.X ∧
    (generateQ S n).1.nq=Fintype.card (state S n).presentation.Q ∧
    (generateQ S n).1.nz=Fintype.card (state S n).presentation.Z ∧
    (generateQ S n).1.nf=Fintype.card (state S n).presentation.Face := by sorry
