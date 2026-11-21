-- Prove2me | Theorems.Thm_QuantumInfo_knillLaflamme_canonicalError
-- name    : QuantumInfo.knillLaflamme_canonicalError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:08.508839+00:00
-- url     : https://prove2.me/theorems/fb032c0a-c7e7-48b2-a736-4bd2e714c828
-- title:
--   Quantum Info: knill Laflamme canonical Error
-- statement:
--   The canonical errors satisfy the **diagonal** Knill–Laflamme condition.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L417-L437
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L417-L437

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
omit [DecidableEq n]

theorem QuantumInfo.knillLaflamme_canonicalError (hc : KnillLaflamme P E c) (k l : ι) :
    P * (canonicalError hc' E k)ᴴ * canonicalError hc' E l * P
      = if k = l then ((hc'.eigenvalues k : ℝ) : ℂ) • P else 0 := by sorry
