-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseBobConditionalSeedWeight_nonneg
-- name    : QuantumParallelRepetition.exactReverseBobConditionalSeedWeight_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T04:56:13.468141+00:00
-- url     : https://prove2.me/theorems/bad07870-f15b-4fc6-a083-0eac929c0ec2
-- title:
--   Nonnegativity of Bob's conditional seed weight
-- statement:
--   With $M$ a finite type with decidable equality, $S \subseteq M$, and $\sigma$ a forward seed on $M$ of forward weight $\mathrm{wt}(\sigma)$, and with $p(S) = 2^{-|M|}\cdot 2|S|/|M|$ the reverse weight of the side $S$, Bob's conditional seed weight is
--   $$w^{B}_{S}(\sigma) = \begin{cases} \mathrm{wt}(\sigma)/p(S), & \text{if the reverse right side of } \sigma \text{ equals } S,\\ 0, & \text{otherwise}.\end{cases}$$
--   The theorem states that $w^{B}_{S}(\sigma) \ge 0$; it is the mirror of the corresponding statement for Alice, differing only in that the side of $\sigma$ compared with $S$ is the reverse right side.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L31590-L31598

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

theorem QuantumParallelRepetition.exactReverseBobConditionalSeedWeight_nonneg
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    0 ≤ exactReverseBobConditionalSeedWeight side seed := by sorry
