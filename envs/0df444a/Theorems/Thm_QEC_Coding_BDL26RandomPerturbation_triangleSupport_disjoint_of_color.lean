-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleSupport_disjoint_of_color
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleSupport_disjoint_of_color
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T21:53:31.931853+00:00
-- url     : https://prove2.me/theorems/bb6c433b-2234-46e8-b7d9-a7f7215bc274
-- title:
--   BDL26 Random Perturbation: triangle Support disjoint of color
-- statement:
--   Disjoint supports in a color class justify independent triangle-hit events.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Coloring.lean#L120-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Coloring.lean#L120-L128

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
noncomputable section
variable (P : TannerSquarePresentation)

theorem QEC.Coding.BDL26RandomPerturbation.triangleSupport_disjoint_of_color {a b : Triangle P} (hne : a ≠ b)
    (hc : triangleColor P a = triangleColor P b) :
    Disjoint (triangleSupport P a) (triangleSupport P b) := by sorry
