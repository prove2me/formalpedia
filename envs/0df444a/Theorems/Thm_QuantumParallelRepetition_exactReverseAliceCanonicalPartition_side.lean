-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceCanonicalPartition_side
-- name    : QuantumParallelRepetition.exactReverseAliceCanonicalPartition_side
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T03:55:35.491808+00:00
-- url     : https://prove2.me/theorems/d87b5445-994a-4029-ad3e-d28b6a7e4432
-- title:
--   The canonical Alice colouring recovers its prescribed side
-- statement:
--   Let $M$ be a finite type with decidable equality, let $S \subseteq M$ be a subset containing a chosen coordinate $i$, and let $b$ be an arbitrary Boolean. Define the *canonical Alice colouring* by
--   $$\pi^{A}_{S,i,b}(j) = \begin{cases} b, & j = i,\\ \mathrm{false}, & j \neq i,\ j \in S,\\ \mathrm{true}, & j \neq i,\ j \notin S.\end{cases}$$
--   The theorem states that, for either value of $b$,
--   $$\{i\} \cup L\big(i, \pi^{A}_{S,i,b}\big) = S ,$$
--   where $L(i,\pi) = \{\, j \neq i : \pi(j) = \mathrm{false} \,\}$. In other words, the reverse left side of the canonical colouring is exactly the prescribed set $S$: the colouring is a right inverse to the map sending a colouring to its reverse left side, and the value at the distinguished coordinate is irrelevant to this.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L31184-L31199

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

theorem QuantumParallelRepetition.exactReverseAliceCanonicalPartition_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    insert coordinate
        (exactLeft coordinate
          (exactReverseAliceCanonicalPartition
            side coordinate ignored)) = side := by sorry
