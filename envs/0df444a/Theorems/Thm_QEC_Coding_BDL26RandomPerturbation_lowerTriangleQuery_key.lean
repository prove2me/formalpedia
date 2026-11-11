-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lowerTriangleQuery_key
-- name    : QEC.Coding.BDL26RandomPerturbation.lowerTriangleQuery_key
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:55:17.555757+00:00
-- url     : https://prove2.me/theorems/f5ad2565-4da2-4651-91d0-ce5147aa5b0d
-- title:
--   BDL26 Random Perturbation: lower Triangle Query key
-- statement:
--   The BDL26 Random Perturbation construction uses the lower Triangle Query key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L13-L18
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L13-L18

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.lowerTriangleQuery_key (P : TannerSquarePresentation) (a b : Triangle P) :
    triangleKey P (lowerTriangleQuery P a b).1 = min (triangleKey P a) (triangleKey P b) := by sorry
