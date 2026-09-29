-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceSideMarkedPosteriorConditional_eq_fixedSeedFiber
-- name    : QuantumParallelRepetition.exactReverseAliceSideMarkedPosteriorConditional_eq_fixedSeedFiber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T14:07:42.760735+00:00
-- url     : https://prove2.me/theorems/0031a426-b846-4b48-8804-55bf9c1136bd
-- title:
--   Conditioning on Alice's marked context collapses the seed mixture to a single seed
-- statement:
--   Assume $|\bar D| > 0$, fix a default letter $y_0 \in Y$, a seed $s$ with distinguished coordinate $i^\ast$ and left reverse side $\Sigma = \{i^\ast\} \cup L$, and a reference outcome $\omega_0$. Compare two laws on pairs (masked context, next Bob question), both grouped by the prefix-mask-and-next-letter code at the marker equal to the rank of $i^\ast$ in $\Sigma$: the first comes from the reverse-Alice next *joint* for the side $\Sigma$, which averages over all seeds according to the reverse-Alice conditional seed law and over outcomes according to the postselected outcome law; the second uses the single fixed seed $s$, grouping outcomes directly by their Alice marked history context and by Bob's question at $i^\ast$. The theorem asserts that these two laws have the same conditional distribution of the next question at the context produced by $\omega_0$. In effect, conditioning on Alice's marked context already pins the seed, so the seed average is invisible.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L55612-L55751

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_23
import Theorems.Thm_QuantumParallelRepetition_exactReverseLeftSide_coordinate_mem
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
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactReverseAliceSideMarkedPosteriorConditional_eq_fixedSeedFiber
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩))
          (exactConditionedReverseAliceNextJoint
            G n S D remaining (exactReverseLeftSide seed)))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseAliceMarkedHistoryContext
              G n S D default seed outcome,
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) := by sorry
