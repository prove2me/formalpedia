-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_clampUnit_quadratic_min
-- name    : QEC.Coding.BDL26RandomPerturbation.clampUnit_quadratic_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:07.102205+00:00
-- url     : https://prove2.me/theorems/57edbd0d-3921-4727-b90c-c202ebc5bd5c
-- title:
--   BDL26 Random Perturbation: clamp Unit quadratic min
-- statement:
--   The BDL26 Random Perturbation construction uses the clamp Unit quadratic min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SegmentProjection.lean#L14-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SegmentProjection.lean#L14-L39

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.clampUnit_quadratic_min {Q D t : ℝ} (hQ : 0 < Q) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Q*(clampUnit (D/Q))^2-2*D*clampUnit (D/Q) ≤ Q*t^2-2*D*t := by sorry
