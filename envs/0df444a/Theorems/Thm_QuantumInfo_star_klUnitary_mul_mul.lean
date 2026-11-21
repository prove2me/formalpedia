-- Prove2me | Theorems.Thm_QuantumInfo_star_klUnitary_mul_mul
-- name    : QuantumInfo.star_klUnitary_mul_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:03.351191+00:00
-- url     : https://prove2.me/theorems/f336e220-7bfd-458b-91fb-ba704e0261ff
-- title:
--   Quantum Info: star kl Unitary mul mul
-- statement:
--   The Quantum Info construction uses the star kl Unitary mul mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L406-L413
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L406-L413

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

theorem QuantumInfo.star_klUnitary_mul_mul :
    star (klUnitary hc') * c * klUnitary hc' = diagonal (RCLike.ofReal ∘ hc'.eigenvalues) := by sorry
