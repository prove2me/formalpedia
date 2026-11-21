-- Prove2me | Theorems.Thm_QuantumInfo_exists_recovery_of_knillLaflamme
-- name    : QuantumInfo.exists_recovery_of_knillLaflamme
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:11.485218+00:00
-- url     : https://prove2.me/theorems/724ddc07-8f90-4c84-8c00-b869bbacf6dc
-- title:
--   Quantum Info: exists recovery of knill Laflamme
-- statement:
--   **The Knill–Laflamme theorem (recovery exists).** If the errors `E` satisfy the
--   Knill–Laflamme condition on the nonzero code `P`, there is a channel `R` with
--   `R (E i ρ E jᴴ) = c j i • ρ` on every code state `ρ = P ρ P`; in particular
--   `R (E i ρ E iᴴ) = c i i • ρ`.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L472-L506
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L472-L506

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

theorem QuantumInfo.exists_recovery_of_knillLaflamme (hP : IsCodeProjector P) (hP0 : P ≠ 0)
    (hc : KnillLaflamme P E c) :
    ∃ R : Channel n n (Option ι), ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P →
      ∀ i j, R.apply (E i * ρ * (E j)ᴴ) = c j i • ρ := by sorry
