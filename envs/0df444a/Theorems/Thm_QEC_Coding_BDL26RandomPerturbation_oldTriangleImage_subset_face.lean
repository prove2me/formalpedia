-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_oldTriangleImage_subset_face
-- name    : QEC.Coding.BDL26RandomPerturbation.oldTriangleImage_subset_face
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:46:06.769072+00:00
-- url     : https://prove2.me/theorems/7eaf62fc-de5c-4e7e-bd1e-fe19161f3540
-- title:
--   BDL26 Random Perturbation: old Triangle Image subset face
-- statement:
--   The BDL26 Random Perturbation construction uses the old Triangle Image subset face property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Density.lean#L54-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Density.lean#L54-L68

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.oldTriangleImage_subset_face (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : Triangle P) : oldTriangleImage P J t ⊆ tannerFaceImage P J t.1 := by sorry
