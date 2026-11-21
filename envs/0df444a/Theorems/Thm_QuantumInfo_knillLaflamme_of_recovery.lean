-- Prove2me | Theorems.Thm_QuantumInfo_knillLaflamme_of_recovery
-- name    : QuantumInfo.knillLaflamme_of_recovery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:36.316316+00:00
-- url     : https://prove2.me/theorems/3ecee160-472f-4db7-9728-d14ba5440e5b
-- title:
--   Quantum Info: knill Laflamme of recovery
-- statement:
--   **The Knill–Laflamme theorem (the condition is necessary).** If a channel `R` corrects the
--   errors `E` on the code `P` up to scalars — `R (E i ρ E iᴴ) = λ i • ρ` on code states — then the
--   errors satisfy the Knill–Laflamme condition.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L689-L707
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L689-L707

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
omit [Fintype ι] [DecidableEq ι]

theorem QuantumInfo.knillLaflamme_of_recovery (hP : IsCodeProjector P) {κ : Type*} [Fintype κ]
    (R : Channel n n κ) (lam : ι → ℂ)
    (h : ∀ i, ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (E i * ρ * (E i)ᴴ) = lam i • ρ) :
    ∃ c : Matrix ι ι ℂ, KnillLaflamme P E c := by sorry
