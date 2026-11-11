-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_colorMatchQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.colorMatchQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:00:32.881423+00:00
-- url     : https://prove2.me/theorems/8b28d965-73d3-40c3-9d87-860d7c48f0b5
-- title:
--   BDL26 Random Perturbation: color Match Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the color Match Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L47-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean#L47-L56

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.colorMatchQuery_cost_le (P : TannerSquarePresentation) (a b : Triangle P) :
    (colorMatchQuery P a b).2 ≤ 6*Fintype.card (Triangle P)*(Fintype.card (Triangle P)+6)+6 := by sorry
