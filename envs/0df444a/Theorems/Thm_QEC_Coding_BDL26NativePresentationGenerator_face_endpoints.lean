-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_face_endpoints
-- name    : QEC.Coding.BDL26NativePresentationGenerator.face_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:59:33.023808+00:00
-- url     : https://prove2.me/theorems/b82e7e8e-23dc-4df6-a63e-0a5e24fbddcf
-- title:
--   BDL26 Native Presentation Generator: face endpoints
-- statement:
--   The literal ordered endpoints, including both original corner bits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3122-L3131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3122-L3131

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

theorem QEC.Coding.BDL26NativePresentationGenerator.face_endpoints (S : OddScale) (n : ℕ) (f : (state S n).presentation.Face) :
    let F := (generateQ S n).1
    let r := generatedRefines S n
    let row := (faceAtQ F.faces (r.fIndex f).val).1
    row.x=(r.xIndex ((state S n).presentation.faceX f)).val ∧
      row.z=(r.zIndex ((state S n).presentation.faceZ f)).val ∧
      row.q0=(r.qIndex ((state S n).presentation.faceQ f 0)).val ∧
      row.q1=(r.qIndex ((state S n).presentation.faceQ f 1)).val := by sorry
