-- Prove2me | Theorems.Thm_QuantumInfo_smul_eq_one_of_unitary
-- name    : QuantumInfo.smul_eq_one_of_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:51:06.730162+00:00
-- url     : https://prove2.me/theorems/0b7447da-633d-4929-b234-e8bb38b64ff3
-- title:
--   Quantum Info: smul eq one of unitary
-- statement:
--   **A unitary error is undone exactly**: if a recovery returns a code state with nonzero trace up
--   to a scalar and the error is unitary, that scalar is `1`, because both the error and the channel
--   preserve the trace.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L828-L838
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L828-L838

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
variable {L : Type*} [Fintype L] [DecidableEq L] {V : Matrix n L ℂ}

theorem QuantumInfo.smul_eq_one_of_unitary {κ : Type*} [Fintype κ] (R : Channel n n κ)
    {E ρ : Matrix n n ℂ} (hE : Eᴴ * E = 1) {γ : ℂ}
    (h : R.apply (E * ρ * Eᴴ) = γ • ρ) (hρ : ρ.trace ≠ 0) : γ = 1 := by sorry
