-- Prove2me | Theorems.Thm_QuantumInfo_knill_laflamme
-- name    : QuantumInfo.knill_laflamme
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:51:11.253052+00:00
-- url     : https://prove2.me/theorems/fa0caff5-31c0-4647-8acc-a80cd6bdae8d
-- title:
--   Quantum Info: knill laflamme
-- statement:
--   **The Knill–Laflamme theorem.** On a nonzero code `P`, the errors `E` satisfy the
--   Knill–Laflamme condition for some matrix `c` if and only if they are correctable: some channel
--   `R`, with any finite number of Kraus operators, undoes each error on every code state up to a
--   scalar.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/Basic.lean#L98-L110
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/Basic.lean#L98-L110

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

theorem QuantumInfo.knill_laflamme {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} (hP : IsCodeProjector P)
    (hP0 : P ≠ 0) :
    (∃ c : Matrix ι ι ℂ, KnillLaflamme P E c) ↔
      ∃ (m : ℕ) (R : Channel n n (Fin m)) (lam : ι → ℂ),
        ∀ i, ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (E i * ρ * (E i)ᴴ) = lam i • ρ := by sorry
