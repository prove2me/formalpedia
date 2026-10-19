-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485FullBilateralWorkRegroup
-- name    : QuantumParallelRepetition.unconditionalActualC485FullBilateralWorkRegroup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.934586+00:00
-- url     : https://prove2.me/theorems/08a7708b-f932-4a4a-8d83-88131c089a95
-- title:
--   QuantumParallelRepetition.unconditionalActualC485FullBilateralWorkRegroup
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

theorem QuantumParallelRepetition.unconditionalActualC485FullBilateralWorkRegroup
    {P N d L m : ℕ}
    (j : Fin L)
    (z : EuclideanSpace ℂ
      (UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m ×
       UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m)) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (Equiv.refl
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m))
          (unconditionalActualC485RetainedHistoryPairEquiv
            (P := P) (N := N) (d := d) j))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv
            (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
              (N := N) (d := d) (m := m)
              (unconditionalActualOneScaleFixedSourcePhaseSplit P) j)
            (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
              (N := N) (d := d) (m := m)
              (unconditionalActualOneScaleFixedSourcePhaseSplit P) j)) z) =
      unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualOneScaleFixedSourcePhaseSplit P) j z := by sorry
