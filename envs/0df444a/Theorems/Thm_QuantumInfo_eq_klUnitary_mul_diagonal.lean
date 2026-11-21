-- Prove2me | Theorems.Thm_QuantumInfo_eq_klUnitary_mul_diagonal
-- name    : QuantumInfo.eq_klUnitary_mul_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:21.728858+00:00
-- url     : https://prove2.me/theorems/94451cef-140c-445a-8935-48fb3ffe328d
-- title:
--   Quantum Info: eq kl Unitary mul diagonal
-- statement:
--   The Quantum Info construction uses the eq kl Unitary mul diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L397-L400
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L397-L400

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

theorem QuantumInfo.eq_klUnitary_mul_diagonal :
    c = klUnitary hc' * diagonal (RCLike.ofReal ∘ hc'.eigenvalues) * star (klUnitary hc') := by sorry
