-- Prove2me | Theorems.Thm_QuantumInfo_Channel_apply_sum
-- name    : QuantumInfo.Channel.apply_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:07.841543+00:00
-- url     : https://prove2.me/theorems/f33c9787-0571-4e4d-ac46-68c4e99368ca
-- title:
--   Channel: apply sum
-- statement:
--   A channel applied to a finite sum.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L139-L143
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L139-L143

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
omit [Fintype ι] [DecidableEq ι]

theorem QuantumInfo.Channel.apply_sum {m κ : Type*} [Fintype m] [Fintype κ] (Φ : Channel n m κ)
    {α : Type*} (s : Finset α) (f : α → Matrix n n ℂ) :
    Φ.apply (∑ a ∈ s, f a) = ∑ a ∈ s, Φ.apply (f a) := by sorry
