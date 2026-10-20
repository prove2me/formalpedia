-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceSelectedRetainedWinningBornGauge
-- name    : QuantumParallelRepetition.unconditionalActualFairSourceSelectedRetainedWinningBornGauge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.934586+00:00
-- url     : https://prove2.me/theorems/cee5592f-b0f6-44e6-a93f-913f23c716cc
-- title:
--   QuantumParallelRepetition.unconditionalActualFairSourceSelectedRetainedWinningBornGauge
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
open WithLp Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualFairSourceSelectedRetainedWinningBornGauge
    {X Y A B τ : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype τ] [DecidableEq τ]
    {P N d m : ℕ}
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × τ)) :
    let e := physical8SelectedGlobalTargetWorkEquiv P N d m
    let U := unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) P alice
    let V := unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) P bob
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (UnconditionalSelectedCopyLocalIndex P d N m ×
          UnconditionalSelectedCopyLocalIndex P d N m) × τ)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM e
            (unitaryConjugatePOVM alice PA))
          (directDSVActualReindexedRetainedPOVM e
            (unitaryConjugatePOVM bob PB)) x y ⊗ₖ
          (1 : Matrix τ τ ℂ))) z =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (UnconditionalSelectedCopyLocalIndex P d N m ×
          UnconditionalSelectedCopyLocalIndex P d N m) × τ)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM e PA)
          (directDSVActualReindexedRetainedPOVM e PB) x y ⊗ₖ
          (1 : Matrix τ τ ℂ)))
      (unconditionalMixedConjugateSelectedBranchLocalAction
        U V z) := by sorry
