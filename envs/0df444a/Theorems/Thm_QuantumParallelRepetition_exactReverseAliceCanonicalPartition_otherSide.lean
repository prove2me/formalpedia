-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceCanonicalPartition_otherSide
-- name    : QuantumParallelRepetition.exactReverseAliceCanonicalPartition_otherSide
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T04:04:48.128801+00:00
-- url     : https://prove2.me/theorems/04c6094b-708a-479e-b4c7-505602fb1fb0
-- title:
--   The canonical Alice partition has the complement of the side as its right block
-- statement:
--   Fix a finite type $M$, a subset $s\subseteq M$, an element $i\in s$ and a bit $b\in\{0,1\}$, and define the canonical colouring $$\pi_{s,i,b}(j)=\begin{cases}b,&j=i,\\0,&j\in s,\ j\neq i,\\1,&j\notin s.\end{cases}$$ Writing $R(i,\pi)=\{j\neq i:\pi(j)=1\}$ for the right block determined by a marked coordinate and a colouring, the theorem states that $R\big(i,\pi_{s,i,b}\big)=M\setminus s$, irrespective of the value of the ignored bit $b$. Thus the canonical colouring is designed so that the block complementary to Alice's side is exactly the set-theoretic complement of $s$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L33174-L33189

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
set_option maxHeartbeats 4200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactReverseAliceCanonicalPartition_otherSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    exactRight coordinate
        (exactReverseAliceCanonicalPartition
          side coordinate ignored) =
      Finset.univ \ side := by sorry
