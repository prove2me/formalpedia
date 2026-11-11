-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QubitBallBounds_mask_card_le
-- name    : QEC.Coding.BDL26QubitBallBounds.mask_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:18:15.153241+00:00
-- url     : https://prove2.me/theorems/3faf8991-b87a-4464-b6ed-208d92a4e73d
-- title:
--   BDL26 Qubit Ball Bounds: mask card le
-- statement:
--   Every literal mask in a ball has the same label budget, even for adaptive masks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/QubitBallBounds.lean#L62-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/QubitBallBounds.lean#L62-L71

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

theorem QEC.Coding.BDL26QubitBallBounds.mask_card_le (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S n J t) (R : ℝ) (center : Space)
    (A : Finset (state S n).presentation.Q)
    (inside : ∀ q ∈ A, dist (J (.q q)) center ≤ R) : A.card ≤ ballBudget t R := by sorry
