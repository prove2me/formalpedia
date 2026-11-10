-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexColor_triangleVertex
-- name    : QEC.Coding.BDL26RandomPerturbation.vertexColor_triangleVertex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:47:31.541996+00:00
-- url     : https://prove2.me/theorems/f651c102-303b-4160-817e-54e12e49c247
-- title:
--   BDL26 Random Perturbation: vertex Color triangle Vertex
-- statement:
--   The BDL26 Random Perturbation construction uses the vertex Color triangle Vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Geometry.lean#L29-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Geometry.lean#L29-L31

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.vertexColor_triangleVertex (P : TannerSquarePresentation) (t : Triangle P) (i : Fin 3) :
    vertexColor P (triangleVertex P t i) = i := by sorry
