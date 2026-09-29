-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseRightSide_coordinate_mem
-- name    : QuantumParallelRepetition.exactReverseRightSide_coordinate_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T03:02:46.941672+00:00
-- url     : https://prove2.me/theorems/2d18e2fc-e68d-447d-b4da-ad5555a2b5aa
-- title:
--   The distinguished coordinate belongs to the reverse right side
-- statement:
--   With $M$ a finite type with decidable equality and $\sigma$ a forward seed on $M$ with distinguished coordinate $i$ and two-colouring $\pi$, write
--   $$R(i,\pi) = \{\, j \in M : j \neq i,\ \pi(j) = \mathrm{true} \,\}$$
--   for the right block and $R^{+}(\sigma) = \{i\} \cup R(i,\pi)$ for the *reverse right side*. The lemma records that $i \in R^{+}(\sigma)$, the mirror image of the corresponding fact for the left side.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L28869-L28873

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_17
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

@[simp] theorem QuantumParallelRepetition.exactReverseRightSide_coordinate_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    seed.coordinate ∈ exactReverseRightSide seed := by sorry
