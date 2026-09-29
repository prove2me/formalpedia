-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exact_source_equation_twenty_seven_support_preserving_of_information
-- name    : QuantumParallelRepetition.exact_source_equation_twenty_seven_support_preserving_of_information
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T15:26:38.212118+00:00
-- url     : https://prove2.me/theorems/5a024de8-6765-4281-af42-9d564401e494
-- title:
--   Support-preserving sampler at the Pinsker rate, from the classical information bound
-- statement:
--   Same setting: positive postselected mass and at least one free coordinate. Assume in addition the classical information bound, namely that both relative entropies $D(P \,\|\, J_A)$ and $D(P \,\|\, J_B)$ are at most the classical information rate $R$ of the conditioning. Then for every $\gamma > 0$ a support-preserving classical sampler in the above sense exists with the accuracy parameter
--   $$
--   \kappa \;=\; \sqrt{R/2},
--   $$
--   the Pinsker rate attached to $G$, $n$, the strategy and $D$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L57545-L57562

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_24
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem
    QuantumParallelRepetition.exact_source_equation_twenty_seven_support_preserving_of_information
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (information : ExactSourceClassicalInformationBound
      G n S D base)
    {gamma : ℝ} (gamma_positive : 0 < gamma) :
    ExactSourceSupportPreservingClassicalSampler
      G n S D base (exactSourcePinskerRate G n S D) gamma := by sorry
