-- Prove2me | Theorems.Thm_QuantumInfo_exists_smul_of_forall_smul
-- name    : QuantumInfo.exists_smul_of_forall_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:16.303256+00:00
-- url     : https://prove2.me/theorems/f5cab3b2-a719-41e2-afde-1729f0b74fa3
-- title:
--   Quantum Info: exists smul of forall smul
-- statement:
--   A matrix mapping every vector `w` to a multiple of `P w`, and vanishing off the code, is a
--   scalar multiple of `P`.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L570-L601
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L570-L601

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

theorem QuantumInfo.exists_smul_of_forall_smul {A : Matrix n n ℂ}
    (hAP : A * P = A) (h : ∀ w : n → ℂ, ∃ α : ℂ, A *ᵥ w = α • (P *ᵥ w)) :
    ∃ μ : ℂ, A = μ • P := by sorry
