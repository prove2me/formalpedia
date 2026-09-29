-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseBobMarkerDecode_rightInverse
-- name    : QuantumParallelRepetition.exactReverseBobMarkerDecode_rightInverse
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T04:03:58.369657+00:00
-- url     : https://prove2.me/theorems/0822be82-b097-48e8-9120-f1b311983ae1
-- title:
--   Decoding a side, context and marker recovers a seed with exactly that code (Bob)
-- statement:
--   Fix a finite type $M$, a subset $s\subseteq M$, a side context $c$ over $s$ and a marker $m\in\{0,\dots,|s|-1\}$. The Bob decoding procedure builds a seed whose marked coordinate is the $m$-th element of $s$ under $c$'s enumeration, whose colouring is the canonical Bob colouring for $(s,i,c\text{'s bit})$, and whose orders and cuts come from $c$ and $m$. The theorem asserts that the Bob encoding of this seed is exactly the original triple: Bob's side is $s$, the induced context is $c$, and the marked coordinate's position is $m$. With injectivity of the encoding this exhibits it as a bijection between seeds and triples of this shape.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L33916-L33997

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_21
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactReverseBobMarkerDecode_rightInverse
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseBobMarkerCode
        (exactReverseBobMarkerDecode
          side context marker) =
      ⟨side, context, marker⟩ := by sorry
