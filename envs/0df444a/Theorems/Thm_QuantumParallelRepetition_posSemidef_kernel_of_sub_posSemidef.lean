-- Prove2me | Theorems.Thm_QuantumParallelRepetition_posSemidef_kernel_of_sub_posSemidef
-- name    : QuantumParallelRepetition.posSemidef_kernel_of_sub_posSemidef
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/330e2e6c-7db3-4e7b-a5e1-333b6ca30a82
-- title:
--   QuantumParallelRepetition.posSemidef_kernel_of_sub_posSemidef
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

theorem QuantumParallelRepetition.posSemidef_kernel_of_sub_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hA : A.PosSemidef) (hsub : (F - A).PosSemidef)
    {x : d → ℂ} (hx : F *ᵥ x = 0) :
    A *ᵥ x = 0 := by sorry
