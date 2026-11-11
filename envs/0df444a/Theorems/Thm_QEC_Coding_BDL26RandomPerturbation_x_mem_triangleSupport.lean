-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_x_mem_triangleSupport
-- name    : QEC.Coding.BDL26RandomPerturbation.x_mem_triangleSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:02:27.39994+00:00
-- url     : https://prove2.me/theorems/6ba5bf7b-dc91-4edf-8658-5b9ef87c01d7
-- title:
--   BDL26 Random Perturbation: x mem triangle Support
-- statement:
--   The BDL26 Random Perturbation construction uses the x mem triangle Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L9-L12
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L9-L12

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.x_mem_triangleSupport (P : TannerSquarePresentation) (a : Triangle P) (x : P.X) :
    Vertex.x x ∈ triangleSupport P a ↔ P.faceX a.1 = x := by sorry
