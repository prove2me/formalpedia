-- Prove2me | Theorems.Thm_SoficGroups_hamming_dichotomy_of_expansion
-- name    : SoficGroups.hamming_dichotomy_of_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/c651d6da-b069-4c1c-89bf-5976c8eb853b
-- title:
--   SoficGroups.hamming_dichotomy_of_expansion
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.hamming_dichotomy_of_expansion {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
          ((Fintype.card V : ℝ) - A.card) ≤
        (boundary σ A : ℝ))
    (c c' : Equiv.Perm V) :
    h * (hammingDist (fun x => c x) (fun x => c' x) : ℝ) ≤
        (permutationCommutationDefect σ c +
          permutationCommutationDefect σ c' : ℕ) ∨
      h * ((Fintype.card V : ℝ) -
          hammingDist (fun x => c x) (fun x => c' x)) ≤
        (permutationCommutationDefect σ c +
          permutationCommutationDefect σ c' : ℕ) := by sorry
