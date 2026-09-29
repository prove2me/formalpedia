-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseRightSide_complement
-- name    : QuantumParallelRepetition.exactReverseRightSide_complement
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T03:32:08.94925+00:00
-- url     : https://prove2.me/theorems/e00d5435-8cca-4216-8d79-f8eb71a45380
-- title:
--   The left block is the complement of the reverse right side
-- statement:
--   Let $M$ be a finite type with decidable equality and $\sigma$ a forward seed on $M$, with distinguished coordinate $i$ and two-colouring $\pi$. With $L(i,\pi)$ and $R(i,\pi)$ the left and right blocks and $R^{+}(\sigma) = \{i\} \cup R(i,\pi)$ the reverse right side, the theorem states that
--   $$L(i,\pi) = M \setminus R^{+}(\sigma) ,$$
--   so that $M$ splits as the reverse right side together with the left block. This is the mirror of the corresponding statement for the reverse left side.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L30598-L30609

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
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactReverseRightSide_complement
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactLeft seed.coordinate seed.partition =
      Finset.univ \ exactReverseRightSide seed := by sorry
