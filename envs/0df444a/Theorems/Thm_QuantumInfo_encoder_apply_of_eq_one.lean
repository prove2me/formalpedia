-- Prove2me | Theorems.Thm_QuantumInfo_encoder_apply_of_eq_one
-- name    : QuantumInfo.encoder_apply_of_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:50:48.14683+00:00
-- url     : https://prove2.me/theorems/55f65400-9488-4f9f-9ede-31b032a683d3
-- title:
--   Quantum Info: encoder apply of eq one
-- statement:
--   The logical action of a single error, for a family containing the identity: the identity's row
--   of the Knill–Laflamme matrix.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L793-L797
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L793-L797

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
omit [Fintype ι] [DecidableEq ι] [Fintype L]

theorem QuantumInfo.encoder_apply_of_eq_one (hP : IsCodeProjector P) (hV : Vᴴ * V = 1) (hPV : P * V = V)
    (hc : KnillLaflamme P E c) {i₀ : ι} (hi₀ : E i₀ = 1) (j : ι) :
    Vᴴ * E j * V = c i₀ j • 1 := by sorry
