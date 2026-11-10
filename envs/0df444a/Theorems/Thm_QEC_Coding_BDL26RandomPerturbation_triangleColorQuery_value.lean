-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleColorQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleColorQuery_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:56:05.769088+00:00
-- url     : https://prove2.me/theorems/624a13af-f5b4-4e32-b572-edcb73d512e5
-- title:
--   BDL26 Random Perturbation: triangle Color Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Color Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean#L85-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean#L85-L89

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare

theorem QEC.Coding.BDL26RandomPerturbation.triangleColorQuery_value (P : TannerSquarePresentation) (a : Triangle P) :
    (triangleColorQuery P a).1 = triangleColor P a := by sorry
