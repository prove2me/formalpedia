-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceCanonicalPartition_unique
-- name    : QuantumParallelRepetition.exactReverseAliceCanonicalPartition_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T04:00:05.094541+00:00
-- url     : https://prove2.me/theorems/4d5e68b3-ed97-4d73-a765-fb6ca91541ee
-- title:
--   Uniqueness of the colouring with a given reverse left side
-- statement:
--   Let $M$ be a finite type with decidable equality, fix $S \subseteq M$ and a coordinate $i$, and let $\pi : M \to \{\mathrm{false},\mathrm{true}\}$ be any colouring whose reverse left side is $S$, that is $\{i\} \cup L(i,\pi) = S$ with $L(i,\pi) = \{\, j \neq i : \pi(j) = \mathrm{false}\,\}$. The theorem asserts that $\pi$ is then forced:
--   $$\pi = \pi^{A}_{S,\,i,\,\pi(i)} ,$$
--   the canonical Alice colouring determined by $S$, $i$ and the value $\pi(i)$. Combined with the previous lemma, which shows the canonical colouring does have reverse left side $S$, this says that the colourings with prescribed reverse left side $S$ are in bijection with the two possible values at the distinguished coordinate — the reverse left side determines the colouring off $i$ completely.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L31201-L31223

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_18
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
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactReverseAliceCanonicalPartition_unique
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (partition : M → Bool)
    (fiber : insert coordinate
      (exactLeft coordinate partition) = side) :
    partition = exactReverseAliceCanonicalPartition
      side coordinate (partition coordinate) := by sorry
