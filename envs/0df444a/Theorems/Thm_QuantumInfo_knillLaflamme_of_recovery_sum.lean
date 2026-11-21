-- Prove2me | Theorems.Thm_QuantumInfo_knillLaflamme_of_recovery_sum
-- name    : QuantumInfo.knillLaflamme_of_recovery_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:32.92089+00:00
-- url     : https://prove2.me/theorems/8844e174-df86-44f4-a4ef-26fe9d48a1b2
-- title:
--   Quantum Info: knill Laflamme of recovery sum
-- statement:
--   **The converse for the combined noise.** If a channel `R` corrects the combined noise
--   `ρ ↦ ∑ᵢ Eᵢ ρ Eᵢᴴ` on the code `P` up to a scalar, the errors satisfy the Knill–Laflamme condition.
--   Every pair `(k, i)` gives the operator `R k Eᵢ P`, and together they satisfy the hypothesis of
--   `exists_smul_of_sum_conj_eq`, so each is a scalar multiple of `P`; trace preservation then gives
--   the condition, as in `knillLaflamme_of_recovery`.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/Basic.lean#L63-L92
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/Basic.lean#L63-L92

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Definitions.Def_KnillLaflammeLean_Basic
set_option autoImplicit false
@[expose] public section
public section
open Matrix
open QuantumInfo
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem QuantumInfo.knillLaflamme_of_recovery_sum {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ}
    (hP : IsCodeProjector P) {κ : Type*} [Fintype κ] (R : Channel n n κ) (lam : ℂ)
    (h : ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (∑ i, E i * ρ * (E i)ᴴ) = lam • ρ) :
    ∃ c : Matrix ι ι ℂ, KnillLaflamme P E c := by sorry
