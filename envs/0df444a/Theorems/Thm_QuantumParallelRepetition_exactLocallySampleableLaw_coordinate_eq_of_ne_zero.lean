-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_coordinate_eq_of_ne_zero
-- name    : QuantumParallelRepetition.exactLocallySampleableLaw_coordinate_eq_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/ef7e122f-a35b-41f9-b24c-2229975a923f
-- title:
--   QuantumParallelRepetition.exactLocallySampleableLaw_coordinate_eq_of_ne_zero
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactLocallySampleableLaw_coordinate_eq_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    t.1 = t.2.2.2.seed.coordinate := by sorry
