-- Prove2me | Theorems.Thm_QuantumInfo_klUnitary_mul_star
-- name    : QuantumInfo.klUnitary_mul_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:53.395958+00:00
-- url     : https://prove2.me/theorems/07d723e6-38c8-4fc2-91c9-91148734c462
-- title:
--   Quantum Info: kl Unitary mul star
-- statement:
--   The Quantum Info construction uses the kl Unitary mul star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L394-L395
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L394-L395

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

theorem QuantumInfo.klUnitary_mul_star : klUnitary hc' * star (klUnitary hc') = 1 := by sorry
