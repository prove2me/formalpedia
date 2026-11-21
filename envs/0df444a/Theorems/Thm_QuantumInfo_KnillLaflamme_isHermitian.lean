-- Prove2me | Theorems.Thm_QuantumInfo_KnillLaflamme_isHermitian
-- name    : QuantumInfo.KnillLaflamme.isHermitian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:37.367181+00:00
-- url     : https://prove2.me/theorems/536f912b-f143-4138-b895-cae6038e2cab
-- title:
--   Knill Laflamme: is Hermitian
-- statement:
--   The Knill–Laflamme matrix of a nonzero code is Hermitian.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L129-L135
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L129-L135

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
omit [DecidableEq n] [Fintype ι] [DecidableEq ι]

theorem QuantumInfo.KnillLaflamme.isHermitian (hP : IsCodeProjector P) (hP0 : P ≠ 0)
    (hc : KnillLaflamme P E c) : c.IsHermitian := by sorry
