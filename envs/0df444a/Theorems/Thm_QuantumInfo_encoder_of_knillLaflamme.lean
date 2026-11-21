-- Prove2me | Theorems.Thm_QuantumInfo_encoder_of_knillLaflamme
-- name    : QuantumInfo.encoder_of_knillLaflamme
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:25.679837+00:00
-- url     : https://prove2.me/theorems/1fee2756-9c0f-4d4f-8f0d-af077eb3f2df
-- title:
--   Quantum Info: encoder of knill Laflamme
-- statement:
--   **Projector form implies encoder form**, for an encoder whose columns are code states.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L777-L788
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L777-L788

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
omit [DecidableEq n] [Fintype ι] [DecidableEq ι] [Fintype L]

theorem QuantumInfo.encoder_of_knillLaflamme (hP : IsCodeProjector P) (hV : Vᴴ * V = 1) (hPV : P * V = V)
    (hc : KnillLaflamme P E c) (i j : ι) : Vᴴ * (E i)ᴴ * E j * V = c i j • 1 := by sorry
