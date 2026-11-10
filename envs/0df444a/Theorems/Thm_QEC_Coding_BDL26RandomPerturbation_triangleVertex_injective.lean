-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleVertex_injective
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleVertex_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:34:31.511858+00:00
-- url     : https://prove2.me/theorems/315ca5c4-dbd3-4231-8984-8980edd8a7f1
-- title:
--   BDL26 Random Perturbation: triangle Vertex injective
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Vertex injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Incidence.lean#L22-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Incidence.lean#L22-L25

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding

theorem QEC.Coding.BDL26RandomPerturbation.triangleVertex_injective (P : TannerSquarePresentation) (t : Triangle P) :
    Function.Injective (triangleVertex P t) := by sorry
