-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_perturbed_segment_lower
-- name    : QEC.Coding.BDL26RandomPerturbation.perturbed_segment_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:48:39.940493+00:00
-- url     : https://prove2.me/theorems/ad1ea28d-ccb2-4713-894e-f65b81d93db5
-- title:
--   BDL26 Random Perturbation: perturbed segment lower
-- statement:
--   Add the original bounded-diameter positions to a radially separated triangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Geometry.lean#L91-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Geometry.lean#L91-L102

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26RandomPerturbation.perturbed_segment_lower (a b c p q s : E) {R k lambda t : ℝ}
    (hR : 0 < R) (hp : ‖p‖ = R) (hpq : ⟪p,q⟫_ℝ ≤ R^2*k)
    (hps : ⟪p,s⟫_ℝ ≤ R^2*k) (hab : ‖a-b‖ ≤ lambda) (hac : ‖a-c‖ ≤ lambda)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    R*(1-k)-lambda ≤ ‖(a+p)-((1-t) • (b+q)+t • (c+s))‖ := by sorry
