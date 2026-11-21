-- Prove2me | Theorems.Thm_QuantumInfo_knillLaflamme_iff
-- name    : QuantumInfo.knillLaflamme_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:15.433412+00:00
-- url     : https://prove2.me/theorems/40e0892f-9c8f-4cdf-9d0b-badc5051efad
-- title:
--   Quantum Info: knill Laflamme iff
-- statement:
--   **The Knill–Laflamme theorem**: the errors `E` are correctable on the nonzero code `P` — some
--   channel inverts every error on the code up to a scalar — if and only if they satisfy the
--   Knill–Laflamme condition for some matrix `c`.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L712-L721
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L712-L721

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

theorem QuantumInfo.knillLaflamme_iff (hP : IsCodeProjector P) (hP0 : P ≠ 0) :
    (∃ c : Matrix ι ι ℂ, KnillLaflamme P E c) ↔
      ∃ (R : Channel n n (Option ι)) (lam : ι → ℂ),
        ∀ i, ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (E i * ρ * (E i)ᴴ) = lam i • ρ := by sorry
