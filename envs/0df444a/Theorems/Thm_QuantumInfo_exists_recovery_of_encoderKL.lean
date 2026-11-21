-- Prove2me | Theorems.Thm_QuantumInfo_exists_recovery_of_encoderKL
-- name    : QuantumInfo.exists_recovery_of_encoderKL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:51:03.59283+00:00
-- url     : https://prove2.me/theorems/bf434bce-a92f-4342-9f6c-9bdbb95b3de2
-- title:
--   Quantum Info: exists recovery of encoder KL
-- statement:
--   **A recovery from the encoder form**: errors that act as scalars on the encoded space are
--   corrected by one channel.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L816-L823
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L816-L823

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

theorem QuantumInfo.exists_recovery_of_encoderKL [Nonempty L] (hV : Vᴴ * V = 1) (h : EncoderKL V E) :
    ∃ (c : Matrix ι ι ℂ) (R : Channel n n (Option ι)),
      ∀ ρ : Matrix n n ℂ, ρ = V * Vᴴ * ρ * (V * Vᴴ) →
        ∀ i j, R.apply (E i * ρ * (E j)ᴴ) = c j i • ρ := by sorry
