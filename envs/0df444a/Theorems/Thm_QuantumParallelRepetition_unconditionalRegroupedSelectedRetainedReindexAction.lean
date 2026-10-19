-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalRegroupedSelectedRetainedReindexAction
-- name    : QuantumParallelRepetition.unconditionalRegroupedSelectedRetainedReindexAction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/a1bd48f2-35f8-4fe9-bd07-5f0fff5d9156
-- title:
--   QuantumParallelRepetition.unconditionalRegroupedSelectedRetainedReindexAction
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

theorem QuantumParallelRepetition.unconditionalRegroupedSelectedRetainedReindexAction
    {κ ι τ δ : Type}
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    [Fintype δ] [DecidableEq δ]
    (e : κ ≃ ι × τ)
    (workEquiv : τ × τ ≃ δ)
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ (κ × κ)) :
    let regroup :=
      (unconditionalSelectedRetainedBilateralRegroup ι τ).trans
        (Equiv.prodCongr (Equiv.refl (ι × ι)) workEquiv)
    let sigma :=
      (Equiv.prodComm ι τ).trans (Equiv.sigmaEquivProd τ ι).symm
    let localEquiv := e.trans sigma
    let A := unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      localEquiv.symm (coherentSharedRandomControlledUnitary
        (fun _ : τ => U))
    let B := unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      localEquiv.symm (coherentSharedRandomControlledUnitary
        (fun _ : τ => V))
    let state := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      ((Equiv.prodCongr e e).trans regroup)
    state
      (toLp 2
        ((((A : Matrix κ κ ℂ) ⊗ₖ
          (B : Matrix κ κ ℂ)).mulVec (ofLp z)))) =
      unconditionalMixedConjugateSelectedBranchLocalAction U V
        (state z) := by sorry
