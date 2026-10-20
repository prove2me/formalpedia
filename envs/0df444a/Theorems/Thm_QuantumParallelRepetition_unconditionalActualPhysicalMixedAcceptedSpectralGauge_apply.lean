-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualPhysicalMixedAcceptedSpectralGauge_apply
-- name    : QuantumParallelRepetition.unconditionalActualPhysicalMixedAcceptedSpectralGauge_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/45240818-4b56-4910-b0c1-8a4485931e52
-- title:
--   QuantumParallelRepetition.unconditionalActualPhysicalMixedAcceptedSpectralGauge_apply
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
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualPhysicalMixedAcceptedSpectralGauge_apply
    {B N d m : ℕ}
    (U : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (φ ψ : Fin B) (i j : Fin d)
    (k l : Fin N) (a b : Fin m) :
    (unconditionalActualCleanedSelectedStageSpectralUnitary
        (B := B) (m := m) U :
        Matrix (UnconditionalSelectedCopyLocalIndex B d N m)
          (UnconditionalSelectedCopyLocalIndex B d N m) ℂ)
      ⟨(φ, i), finProdFinEquiv (k, a)⟩
      ⟨(ψ, j), finProdFinEquiv (l, b)⟩ =
        if φ = ψ then
          (U : Matrix
              (DSVUniformDensityThresholdLocalIndex N d)
              (DSVUniformDensityThresholdLocalIndex N d) ℂ)
            ⟨k, i⟩ ⟨l, j⟩ *
            (if a = b then (1 : ℂ) else 0)
        else 0 := by sorry
