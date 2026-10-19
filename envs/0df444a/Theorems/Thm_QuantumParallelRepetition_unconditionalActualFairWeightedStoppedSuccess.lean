-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairWeightedStoppedSuccess
-- name    : QuantumParallelRepetition.unconditionalActualFairWeightedStoppedSuccess
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.934586+00:00
-- url     : https://prove2.me/theorems/6e945526-3d2d-4b69-b419-df246a9f7284
-- title:
--   QuantumParallelRepetition.unconditionalActualFairWeightedStoppedSuccess
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
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualFairWeightedStoppedSuccess
    {I : Type} [Fintype I]
    {S B N d L m : Nat}
    (weight : I → ℝ)
    (weight_normalized : (∑ h : I, weight h) = 1)
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : I → BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (async terminal : ℝ)
    (asynchronous_bound :
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule (ξ h) (ζ h)) ≤ async)
    (terminal_bound :
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N width schedule (ξ h) (ζ h)) ≤ terminal) :
    1 - (async + terminal) ≤
      ∑ h : I, weight h *
        ∑ j : Fin L,
          ‖integratorActualC485CleanedVector
            Q width schedule (ξ h) (ζ h) A C j‖ ^ 2 := by sorry
