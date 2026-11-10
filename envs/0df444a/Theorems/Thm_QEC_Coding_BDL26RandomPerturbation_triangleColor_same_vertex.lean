-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleColor_same_vertex
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleColor_same_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:51:40.127502+00:00
-- url     : https://prove2.me/theorems/a967724e-1b73-467b-b7be-267bf99b4289
-- title:
--   BDL26 Random Perturbation: triangle Color same vertex
-- statement:
--   Equal colors and a common domain vertex force the same triangle label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Coloring.lean#L101-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Coloring.lean#L101-L117

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
noncomputable section
variable (P : TannerSquarePresentation)

theorem QEC.Coding.BDL26RandomPerturbation.triangleColor_same_vertex {a b : Triangle P}
    (hc : triangleColor P a = triangleColor P b) {i j : Fin 3}
    (hv : triangleVertex P a i = triangleVertex P b j) : a = b := by sorry
