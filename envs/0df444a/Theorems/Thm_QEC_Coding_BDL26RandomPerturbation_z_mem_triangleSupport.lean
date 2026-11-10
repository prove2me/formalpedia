-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_z_mem_triangleSupport
-- name    : QEC.Coding.BDL26RandomPerturbation.z_mem_triangleSupport
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:02:42.918862+00:00
-- url     : https://prove2.me/theorems/f2cf284c-c89d-4afc-89d0-4c0aab5b4d6a
-- title:
--   BDL26 Random Perturbation: z mem triangle Support
-- statement:
--   The BDL26 Random Perturbation construction uses the z mem triangle Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L19-L22
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L19-L22

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.z_mem_triangleSupport (P : TannerSquarePresentation) (a : Triangle P) (z : P.Z) :
    Vertex.z z ∈ triangleSupport P a ↔ P.faceZ a.1 = z := by sorry
