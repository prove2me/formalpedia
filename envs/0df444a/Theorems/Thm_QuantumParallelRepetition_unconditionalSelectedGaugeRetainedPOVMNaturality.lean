-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedGaugeRetainedPOVMNaturality
-- name    : QuantumParallelRepetition.unconditionalSelectedGaugeRetainedPOVMNaturality
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.934586+00:00
-- url     : https://prove2.me/theorems/35aa32e0-6807-4822-a15c-3ae64f119cbe
-- title:
--   QuantumParallelRepetition.unconditionalSelectedGaugeRetainedPOVMNaturality
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

theorem QuantumParallelRepetition.unconditionalSelectedGaugeRetainedPOVMNaturality
    {C : Type} [Fintype C]
    {P N d m : ℕ}
    (basis : Matrix.unitaryGroup (Fin d) ℂ)
    (source : POVM C (Fin d)) :
    directDSVActualReindexedRetainedPOVM
        (physical8SelectedGlobalTargetWorkEquiv P N d m)
        (unitaryConjugatePOVM basis source) =
      unitaryConjugatePOVM
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P basis)
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          source) := by sorry
