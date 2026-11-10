-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_oldTriangleImage_smul
-- name    : QEC.Coding.BDL26RandomPerturbation.oldTriangleImage_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:45:45.397193+00:00
-- url     : https://prove2.me/theorems/ebb359b5-dabc-4dcb-b14f-191f9cae031a
-- title:
--   BDL26 Random Perturbation: old Triangle Image smul
-- statement:
--   The BDL26 Random Perturbation construction uses the old Triangle Image smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Density.lean#L42-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Density.lean#L42-L52

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.oldTriangleImage_smul (P : TannerSquarePresentation) (J : Vertex P → Space)
    (a : ℝ) (t : Triangle P) :
    oldTriangleImage P (fun v => a • J v) t =
      (fun p => a • p) '' oldTriangleImage P J t := by sorry
