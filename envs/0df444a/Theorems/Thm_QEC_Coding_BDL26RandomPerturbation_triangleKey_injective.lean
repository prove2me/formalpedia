-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleKey_injective
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleKey_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:50:51.308988+00:00
-- url     : https://prove2.me/theorems/1c0cd0b9-6f2d-4167-af84-56c1125d505c
-- title:
--   BDL26 Random Perturbation: triangle Key injective
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Key injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Coloring.lean#L68-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Coloring.lean#L68-L71

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
noncomputable section
variable (P : TannerSquarePresentation)

theorem QEC.Coding.BDL26RandomPerturbation.triangleKey_injective : Function.Injective (triangleKey P) := by sorry
