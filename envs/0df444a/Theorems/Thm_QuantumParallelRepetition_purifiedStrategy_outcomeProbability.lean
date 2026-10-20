-- Prove2me | Theorems.Thm_QuantumParallelRepetition_purifiedStrategy_outcomeProbability
-- name    : QuantumParallelRepetition.purifiedStrategy_outcomeProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/594416f2-1a08-41ea-a7c5-167ea0455446
-- title:
--   QuantumParallelRepetition.purifiedStrategy_outcomeProbability
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.purifiedStrategy_outcomeProbability
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G)
    (x : X) (y : Y) (a : A) (b : B) :
    (purifiedStrategy S).outcomeProbability x y a b =
      S.outcomeProbability x y a b := by sorry
