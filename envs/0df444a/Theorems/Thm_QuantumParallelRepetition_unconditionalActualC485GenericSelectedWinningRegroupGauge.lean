-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485GenericSelectedWinningRegroupGauge
-- name    : QuantumParallelRepetition.unconditionalActualC485GenericSelectedWinningRegroupGauge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:49.795984+00:00
-- url     : https://prove2.me/theorems/d702052c-376b-462f-b003-2078c5d9ff48
-- title:
--   QuantumParallelRepetition.unconditionalActualC485GenericSelectedWinningRegroupGauge
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
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.unconditionalActualC485GenericSelectedWinningRegroupGauge
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ} {ι κ R T : Type}
    [Fintype ι] [Fintype κ] [Fintype R] [Fintype T]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq R] [DecidableEq T]
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ)) :
    let selected := UnconditionalSelectedCopyLocalIndex P d N m
    let stage := physical8SelectedGlobalTargetWorkEquiv P N d m
    let gaugedAlice := directDSVActualReindexedRetainedPOVM stage
      (unitaryConjugatePOVM alice PA)
    let gaugedBob := directDSVActualReindexedRetainedPOVM stage
      (unitaryConjugatePOVM bob PB)
    let plainAlice := directDSVActualReindexedRetainedPOVM stage PA
    let plainBob := directDSVActualReindexedRetainedPOVM stage PB
    let regrouped :=
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr (Equiv.refl (selected × selected)) pair)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv eA eB) z)
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM eA gaugedAlice)
          (directDSVActualReindexedRetainedPOVM eB gaugedBob)
          x y)) z =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (selected × selected) × T) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          plainAlice plainBob x y ⊗ₖ (1 : Matrix T T ℂ)))
      (unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        regrouped) := by sorry
