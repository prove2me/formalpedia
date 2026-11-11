-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QubitBallBounds_supported_word_weight_le
-- name    : QEC.Coding.BDL26QubitBallBounds.supported_word_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:34:05.729124+00:00
-- url     : https://prove2.me/theorems/117d246b-bc37-43dc-8899-8299e765418b
-- title:
--   BDL26 Qubit Ball Bounds: supported word weight le
-- statement:
--   Only the nonzero support of a word must lie in the ball. The mask used
--   by a caller may also contain zero-valued coordinates outside it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/QubitBallBounds.lean#L75-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/QubitBallBounds.lean#L75-L83

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

theorem QEC.Coding.BDL26QubitBallBounds.supported_word_weight_le {F : Type*} [Zero F] [DecidableEq F]
    (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S n J t) (R : ℝ) (center : Space)
    (w : QEC.Coding.Word F (state S n).presentation.Q)
    (inside : ∀ q ∈ QEC.Coding.hammingSupport w, dist (J (.q q)) center ≤ R) :
    QEC.Coding.HammingWeight w ≤ ballBudget t R := by sorry
