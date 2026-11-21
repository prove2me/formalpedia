-- Prove2me | Theorems.Thm_QuantumInfo_exists_smul_of_sum_conj_eq
-- name    : QuantumInfo.exists_smul_of_sum_conj_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:31.684325+00:00
-- url     : https://prove2.me/theorems/225b1228-5042-42e6-953c-34250b9a30b4
-- title:
--   Quantum Info: exists smul of sum conj eq
-- statement:
--   **Kraus operators of a scalar map on the code are scalars.** If
--   `∑ₖ A k X (A k)ᴴ = λ • P X P` for every `X`, and each `A k` vanishes off the code, then every
--   `A k` is a scalar multiple of `P`.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L607-L664
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L607-L664

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

theorem QuantumInfo.exists_smul_of_sum_conj_eq {κ : Type*} [Fintype κ] (hP : IsCodeProjector P)
    (A : κ → Matrix n n ℂ) (lam : ℂ) (hA : ∀ k, A k * P = A k)
    (h : ∀ X : Matrix n n ℂ, ∑ k, A k * X * (A k)ᴴ = lam • (P * X * P)) (k : κ) :
    ∃ μ : ℂ, A k = μ • P := by sorry
