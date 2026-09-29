-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceConditionalSeedWeight_nonneg
-- name    : QuantumParallelRepetition.exactReverseAliceConditionalSeedWeight_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T05:11:14.634719+00:00
-- url     : https://prove2.me/theorems/e1c403d3-6535-4d3d-a0bf-de0dbcc9b6e9
-- title:
--   Nonnegativity of Alice's conditional seed weight
-- statement:
--   Let $M$ be a finite type with decidable equality, let $S \subseteq M$, and let $\sigma$ be a forward seed on $M$, that is a distinguished coordinate, a two-colouring, orderings of the two colour classes and a cut point in each. Write $\mathrm{wt}(\sigma)$ for the forward seed weight, the probability of $\sigma$ under independent uniform choices of these data, and
--   $$p(S) = 2^{-|M|}\cdot \frac{2\,|S|}{|M|}$$
--   for the reverse weight of the side $S$. Alice's conditional seed weight is defined by
--   $$w^{A}_{S}(\sigma) = \begin{cases} \mathrm{wt}(\sigma)/p(S), & \text{if the reverse left side of } \sigma \text{ equals } S,\\ 0, & \text{otherwise},\end{cases}$$
--   and the theorem states that $w^{A}_{S}(\sigma) \ge 0$ for all $S$ and $\sigma$. This is the basic positivity fact needed before $w^{A}_{S}$ can be used as the weight of a probability law on seeds conditioned on the observed side.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L31580-L31588

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_20
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactReverseAliceConditionalSeedWeight_nonneg
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    0 ≤ exactReverseAliceConditionalSeedWeight side seed := by sorry
