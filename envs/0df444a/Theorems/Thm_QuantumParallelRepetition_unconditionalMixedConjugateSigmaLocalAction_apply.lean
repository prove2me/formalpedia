-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateSigmaLocalAction_apply
-- name    : QuantumParallelRepetition.unconditionalMixedConjugateSigmaLocalAction_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/75949246-f2cb-48d3-9cb7-ee9a805ab9f8
-- title:
--   QuantumParallelRepetition.unconditionalMixedConjugateSigmaLocalAction_apply
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

theorem QuantumParallelRepetition.unconditionalMixedConjugateSigmaLocalAction_apply
    {d m : ℕ} (B : ℕ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
        (Σ _ : Fin B × Fin d, Fin m)))
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin m) :
    unconditionalMixedConjugateSigmaLocalAction B U V z
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      ∑ k : Fin d, ∑ l : Fin d,
        (U : Matrix (Fin d) (Fin d) ℂ) i k *
        (V : Matrix (Fin d) (Fin d) ℂ) j l *
        z (⟨(φ, k), a⟩, ⟨(ψ, l), b⟩) := by sorry
