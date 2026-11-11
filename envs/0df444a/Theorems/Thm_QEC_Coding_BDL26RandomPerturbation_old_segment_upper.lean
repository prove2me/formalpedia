-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_old_segment_upper
-- name    : QEC.Coding.BDL26RandomPerturbation.old_segment_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:47:54.6757+00:00
-- url     : https://prove2.me/theorems/9f501edf-a26a-4da2-90f6-4d190ab1c6ae
-- title:
--   BDL26 Random Perturbation: old segment upper
-- statement:
--   A triangle of diameter at most lambda moves its opposite convex segment by at most lambda.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Geometry.lean#L75-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Geometry.lean#L75-L88

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26RandomPerturbation.old_segment_upper (a b c : E) {lambda t : ℝ}
    (hab : ‖a-b‖ ≤ lambda) (hac : ‖a-c‖ ≤ lambda) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖a - ((1-t) • b + t • c)‖ ≤ lambda := by sorry
