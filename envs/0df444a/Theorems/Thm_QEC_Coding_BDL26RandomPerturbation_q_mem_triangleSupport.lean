-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_q_mem_triangleSupport
-- name    : QEC.Coding.BDL26RandomPerturbation.q_mem_triangleSupport
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:02:09.91159+00:00
-- url     : https://prove2.me/theorems/7170cf76-e592-4324-9ccb-d7a41e97ff27
-- title:
--   BDL26 Random Perturbation: q mem triangle Support
-- statement:
--   The BDL26 Random Perturbation construction uses the q mem triangle Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L14-L17
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L14-L17

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.q_mem_triangleSupport (P : TannerSquarePresentation) (a : Triangle P) (q : P.Q) :
    Vertex.q q ∈ triangleSupport P a ↔ P.faceQ a.1 a.2 = q := by sorry
