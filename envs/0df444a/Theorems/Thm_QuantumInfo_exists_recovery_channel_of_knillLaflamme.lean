-- Prove2me | Theorems.Thm_QuantumInfo_exists_recovery_channel_of_knillLaflamme
-- name    : QuantumInfo.exists_recovery_channel_of_knillLaflamme
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:41.686213+00:00
-- url     : https://prove2.me/theorems/11798e79-53fb-4956-98bd-5b414c38eee2
-- title:
--   Quantum Info: exists recovery channel of knill Laflamme
-- statement:
--   **A noise channel satisfying Knill–Laflamme is corrected on the code**: for a channel `𝓔`
--   whose Kraus operators satisfy the condition, `R (𝓔 ρ) = ρ` for every `ρ = P ρ P`.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L510-L528
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L510-L528

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
set_option autoImplicit false
@[expose] public section
public section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
open QuantumInfo
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} {c : Matrix ι ι ℂ}

theorem QuantumInfo.exists_recovery_channel_of_knillLaflamme (hP : IsCodeProjector P) (hP0 : P ≠ 0)
    (𝓔 : Channel n n ι) (hc : KnillLaflamme P 𝓔.kraus c) :
    ∃ R : Channel n n (Option ι), ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P →
      R.apply (𝓔.apply ρ) = ρ := by sorry
