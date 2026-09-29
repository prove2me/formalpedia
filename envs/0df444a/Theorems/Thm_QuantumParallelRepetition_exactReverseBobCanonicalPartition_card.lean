-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseBobCanonicalPartition_card
-- name    : QuantumParallelRepetition.exactReverseBobCanonicalPartition_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T04:46:30.847737+00:00
-- url     : https://prove2.me/theorems/fe854bbc-4546-4dbf-8269-3c3ea86480f7
-- title:
--   The right block of the canonical Bob partition has one element fewer than the side
-- statement:
--   Let $M$ be a finite type, $s\subseteq M$, $i\in s$ and $b\in\{0,1\}$, and let $\pi^{\mathrm{B}}_{s,i,b}$ be the canonical Bob colouring, which sends $i$ to $b$, every other element of $s$ to $1$, and everything outside $s$ to $0$. Writing $R(i,\pi)=\{j\neq i:\pi(j)=1\}$, the theorem states $$\big|R\big(i,\pi^{\mathrm{B}}_{s,i,b}\big)\big|+1=|s| ,$$ the counterpart for Bob of the cardinality identity for the canonical Alice colouring.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L33220-L33230

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_19
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactReverseBobCanonicalPartition_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    (exactRight coordinate
      (exactReverseBobCanonicalPartition
        side coordinate ignored)).card + 1 = side.card := by sorry
