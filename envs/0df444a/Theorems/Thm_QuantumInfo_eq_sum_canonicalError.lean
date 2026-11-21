-- Prove2me | Theorems.Thm_QuantumInfo_eq_sum_canonicalError
-- name    : QuantumInfo.eq_sum_canonicalError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:09.04877+00:00
-- url     : https://prove2.me/theorems/4896309b-9536-4810-8361-44f285835706
-- title:
--   Quantum Info: eq sum canonical Error
-- statement:
--   The errors in terms of the canonical ones: `E i = ∑ₖ conj(U i k) • F k`.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L441-L454
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L441-L454

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
omit [Fintype n] [DecidableEq n]

theorem QuantumInfo.eq_sum_canonicalError (i : ι) :
    E i = ∑ k, star (klUnitary hc' i k) • canonicalError hc' E k := by sorry
