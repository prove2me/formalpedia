-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseRightSide_card
-- name    : QuantumParallelRepetition.exactReverseRightSide_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T03:11:20.035429+00:00
-- url     : https://prove2.me/theorems/10ebbd02-8c5f-4587-8f72-774e825cf079
-- title:
--   Cardinality of the reverse right side
-- statement:
--   Let $\sigma$ be a forward seed on a finite type $M$ with decidable equality, with distinguished coordinate $i$ and two-colouring $\pi$, right block $R(i,\pi) = \{\, j \neq i : \pi(j) = \mathrm{true} \,\}$ and reverse right side $R^{+}(\sigma) = \{i\} \cup R(i,\pi)$. Then
--   $$|R^{+}(\sigma)| = |R(i,\pi)| + 1 ,$$
--   since the distinguished coordinate is excluded from the right block and therefore contributes one new element.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L28883-L28889

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_17
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
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

theorem QuantumParallelRepetition.exactReverseRightSide_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (exactReverseRightSide seed).card =
      (exactRight seed.coordinate seed.partition).card + 1 := by sorry
