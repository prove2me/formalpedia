-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_cap_near_axis
-- name    : QEC.Coding.BDL26RandomPerturbation.cap_near_axis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:47:41.75316+00:00
-- url     : https://prove2.me/theorems/51b4e517-5f3e-4bd6-ab39-7bb4e1c61407
-- title:
--   BDL26 Random Perturbation: cap near axis
-- statement:
--   A sufficiently narrow actual cap lies close to its axis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Geometry.lean#L34-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Geometry.lean#L34-L43

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.cap_near_axis (u s : Sphere) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 24)
    (hs : s ∈ cap u (Real.cos θ)) : ‖(s : Space) - (u : Space)‖ ≤ 1 / 8 := by sorry
