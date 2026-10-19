-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFixedSourceFullBilateralRegroup_eq
-- name    : QuantumParallelRepetition.unconditionalActualFixedSourceFullBilateralRegroup_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.052979+00:00
-- url     : https://prove2.me/theorems/deb365ac-2d8a-4f1e-b9ef-ccbc66892eef
-- title:
--   QuantumParallelRepetition.unconditionalActualFixedSourceFullBilateralRegroup_eq
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

theorem QuantumParallelRepetition.unconditionalActualFixedSourceFullBilateralRegroup_eq
    {B N d L m : ℕ} {R : Type} (j : Fin L) :
    unconditionalSourcePhysicalCleanedFullBilateralRegroup
        (R := R) (B := B) (N := N) (d := d) (m := m) j =
      (unconditionalSelectedRetainedBilateralRegroup
        (UnconditionalSelectedCopyLocalIndex B d N m)
        (UnconditionalActualCleanedSelectedRetainedIndex
          (N := N) (d := d) j R)).trans
        (Equiv.prodCongr
          (Equiv.refl
            (UnconditionalSelectedCopyLocalIndex B d N m ×
             UnconditionalSelectedCopyLocalIndex B d N m))
          (unconditionalActualFixedSourceRetainedHistoryPairEquiv
            (N := N) (d := d) (R := R) j)) := by sorry
