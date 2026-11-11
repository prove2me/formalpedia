-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QubitBallBounds_integer_ball_card
-- name    : QEC.Coding.BDL26QubitBallBounds.integer_ball_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:31:29.272191+00:00
-- url     : https://prove2.me/theorems/c3ab4ed2-9f16-4978-b110-36a0f02e60c9
-- title:
--   BDL26 Qubit Ball Bounds: integer ball card
-- statement:
--   Integer-radius bounds follow from labelled unit density without injectivity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/QubitBallBounds.lean#L28-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/QubitBallBounds.lean#L28-L37

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26QubitBallBounds
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26CSSHamiltonian
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26QubitBallBounds.integer_ball_card (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S n J t) (K : Nat) (center : Space) :
    ((qubitHits (state S n).presentation J (Metric.closedBall center K)).card : ℝ) ≤
      ((2*K+1 : Nat)^3 : ℝ)*(2*t) := by sorry
