-- Prove2me | Theorems.Thm_QuantumInfo_knill_laflamme_sum
-- name    : QuantumInfo.knill_laflamme_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:51:18.427434+00:00
-- url     : https://prove2.me/theorems/c4d54195-727b-4b47-bc26-a50444b12912
-- title:
--   Quantum Info: knill laflamme sum
-- statement:
--   **The Knill–Laflamme theorem for the combined noise.** On a nonzero code `P`, the errors `E`
--   satisfy the Knill–Laflamme condition for some matrix `c` if and only if some channel `R`, with any
--   finite number of Kraus operators, undoes the combined noise `ρ ↦ ∑ᵢ Eᵢ ρ Eᵢᴴ` on every code state
--   up to a scalar. The errors need not form a channel.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/Basic.lean#L116-L128
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/Basic.lean#L116-L128

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

theorem QuantumInfo.knill_laflamme_sum {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} (hP : IsCodeProjector P)
    (hP0 : P ≠ 0) :
    (∃ c : Matrix ι ι ℂ, KnillLaflamme P E c) ↔
      ∃ (m : ℕ) (R : Channel n n (Fin m)) (lam : ℂ),
        ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (∑ i, E i * ρ * (E i)ᴴ) = lam • ρ := by sorry
