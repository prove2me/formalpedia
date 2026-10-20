-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalCompleteProjectiveOutcome_eq_blockVector
-- name    : QuantumParallelRepetition.dSVDensityRationalCompleteProjectiveOutcome_eq_blockVector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/f4f53d20-4038-4710-a047-0a89f875bfdb
-- title:
--   QuantumParallelRepetition.dSVDensityRationalCompleteProjectiveOutcome_eq_blockVector
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

theorem QuantumParallelRepetition.dSVDensityRationalCompleteProjectiveOutcome_eq_blockVector
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (a b : Bool) :
    dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ a b =
      (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) •
        toLp 2
          (Matrix.vec
            ((Matrix.blockDiagonal' fun k : Fin N =>
              (dSVDensityRationalLeftProjectiveThresholdPOVM
                  w N k ξ).effect a *
                (dSVDensityRationalLeftProjectiveThresholdPOVM
                  w N k ζ).effect b).transpose)) := by sorry
