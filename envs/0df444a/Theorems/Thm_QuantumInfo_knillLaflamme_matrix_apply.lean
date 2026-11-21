-- Prove2me | Theorems.Thm_QuantumInfo_knillLaflamme_matrix_apply
-- name    : QuantumInfo.knillLaflamme_matrix_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:10.618064+00:00
-- url     : https://prove2.me/theorems/306ecef1-e6d5-4329-827d-5c38f28a1f5f
-- title:
--   Quantum Info: knill Laflamme matrix apply
-- statement:
--   The Knill–Laflamme matrix in terms of the eigen-data: `c j i = ∑ₖ U j k d k conj(U i k)`.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L457-L462
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L457-L462

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
variable (hc' : c.IsHermitian)

theorem QuantumInfo.knillLaflamme_matrix_apply (i j : ι) :
    c j i = ∑ k, klUnitary hc' j k * (hc'.eigenvalues k : ℂ) * star (klUnitary hc' i k) := by sorry
