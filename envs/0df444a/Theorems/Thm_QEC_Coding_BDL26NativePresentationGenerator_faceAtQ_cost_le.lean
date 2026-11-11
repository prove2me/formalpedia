-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_faceAtQ_cost_le
-- name    : QEC.Coding.BDL26NativePresentationGenerator.faceAtQ_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:43:27.326946+00:00
-- url     : https://prove2.me/theorems/04d5d1c7-26c7-478a-82cc-fb340045fd3f
-- title:
--   BDL26 Native Presentation Generator: face At Q cost le
-- statement:
--   The BDL26 Native Presentation Generator construction uses the face At Q cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L474-L484
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L474-L484

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

theorem QEC.Coding.BDL26NativePresentationGenerator.faceAtQ_cost_le (fs : List FaceRow) (i : ℕ) :
    (faceAtQ fs i).2≤2*fs.length+1 := by sorry
