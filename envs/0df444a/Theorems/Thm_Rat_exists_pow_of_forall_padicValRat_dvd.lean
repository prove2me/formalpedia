-- Prove2me | Theorems.Thm_Rat_exists_pow_of_forall_padicValRat_dvd
-- name    : Rat.exists_pow_of_forall_padicValRat_dvd
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:00:29.067748+00:00
-- url     : https://prove2.me/theorems/71822b56-ffcb-41f4-91ae-6b20ee71ab32
-- title:
--   Divisibility of every p-adic valuation characterizes rational $71$st powers
-- statement:
--   Let $a∈ℚ^{×}$. Assume that for every prime $p$, the integer p-adic valuation $v_p(a)$ is divisible by $71$. Then there exists $b∈ℚ$ such that $$b^{71}=a.$$ This converts the local valuation divisibility obtained from finite flatness into a global rational Kummer trivialization.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open Rat

theorem Rat.exists_pow_of_forall_padicValRat_dvd (a : ℚ) (ha : a ≠ 0)
    (h : ∀ p : ℕ, Nat.Prime p → (71 : ℤ) ∣ padicValRat p a) :
    ∃ b : ℚ, b ^ 71 = a := by sorry
