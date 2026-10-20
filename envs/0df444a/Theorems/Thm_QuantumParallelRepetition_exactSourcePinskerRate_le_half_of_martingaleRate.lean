-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactSourcePinskerRate_le_half_of_martingaleRate
-- name    : QuantumParallelRepetition.exactSourcePinskerRate_le_half_of_martingaleRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/9a6fd5e8-4b21-40f4-8991-b67cf81580c6
-- title:
--   QuantumParallelRepetition.exactSourcePinskerRate_le_half_of_martingaleRate
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
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactSourcePinskerRate_le_half_of_martingaleRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    {rateTolerance : ℝ} (rate_nonnegative : 0 ≤ rateTolerance)
    (rate_bound :
      martingaleRate G n S D ≤ rateTolerance ^ 2 / 8) :
    exactSourcePinskerRate G n S D ≤ rateTolerance / 2 := by sorry
