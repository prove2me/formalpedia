-- Prove2me | Theorems.Thm_QuarterSumLadder_gauss_lehmer_product
-- name    : QuarterSumLadder.gauss_lehmer_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:42.058785+00:00
-- url     : https://prove2.me/theorems/1c008606-d697-5962-97e5-b877f961c049
-- title:
--   Quarter Sum Ladder: gauss lehmer product
-- statement:
--   **The Gauss–Lehmer product** (the input to the quartic Gauss lemma): if `A` is a set of nonzero
--   elements of the half system `0 < ⟨x⟩ < p/2` stable under `x ↦ 2x` (for `⟨x⟩ < p/4`) and
--   `x ↦ -2x` (otherwise), then `2^{|A|} (-1)^{#\{x ∈ A : ⟨x⟩ > p/4\}} = 1` in `ZMod p`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L60-L64
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L60-L64

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.gauss_lehmer_product (hp2 : p ≠ 2) (A : Finset (ZMod p))
    (hA : ∀ x ∈ A, x ≠ 0 ∧ 2 * x.val < p)
    (hφ : ∀ x ∈ A, (if 4 * x.val < p then 2 * x else -(2 * x)) ∈ A) :
    (2 : ZMod p) ^ A.card * (-1) ^ (A.filter fun x => ¬ 4 * x.val < p).card = 1 := by sorry
