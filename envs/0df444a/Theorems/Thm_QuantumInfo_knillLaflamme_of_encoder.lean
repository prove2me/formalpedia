-- Prove2me | Theorems.Thm_QuantumInfo_knillLaflamme_of_encoder
-- name    : QuantumInfo.knillLaflamme_of_encoder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:23.285058+00:00
-- url     : https://prove2.me/theorems/05f9f791-af87-4d2c-8653-9fbde140860e
-- title:
--   Quantum Info: knill Laflamme of encoder
-- statement:
--   **Encoder form implies projector form.** If the errors are scalar on the encoded space,
--   `Vᴴ Eᵢᴴ Eⱼ V = cᵢⱼ • 1`, they satisfy Knill–Laflamme on the code `V Vᴴ`. This needs no rank
--   statement about `V Vᴴ`, and not even that `V` is an isometry.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L765-L773
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L765-L773

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
omit [DecidableEq n] [Fintype ι] [DecidableEq ι]

theorem QuantumInfo.knillLaflamme_of_encoder
    (h : ∀ i j, Vᴴ * (E i)ᴴ * E j * V = c i j • 1) :
    KnillLaflamme (V * Vᴴ) E c := by sorry
