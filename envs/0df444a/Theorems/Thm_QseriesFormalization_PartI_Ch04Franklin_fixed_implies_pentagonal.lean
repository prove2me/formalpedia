-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04Franklin_fixed_implies_pentagonal
-- name    : QseriesFormalization.PartI.Ch04Franklin.fixed_implies_pentagonal
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:25:07.049511+00:00
-- url     : https://prove2.me/theorems/9669b729-0660-426c-8625-1ada3f2a8c1c
-- title:
--   Fixed points of Franklin's involution have pentagonal shape
-- statement:
--   Let $S$ be a nonempty finite set of positive naturals fixed by Franklin's involution, $\mathrm{franklinInv}(S)=S$. Then there is an integer $k\ge1$ such that
--   $$S=\{k,k+1,\dots,2k-1\}\quad\text{or}\quad S=\{k+1,k+2,\dots,2k\}.$$
--   These are the strict partitions into $k$ consecutive parts of sizes $k(3k-1)/2$ and $k(3k+1)/2$ respectively, i.e. the generalized pentagonal numbers. This is a step in the Franklin-involution proof of Euler's pentagonal number theorem.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 5. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter05_Franklin.lean#L889-L962

import Definitions.Def_QseriesFormalization_Chapter05_Franklin
import Mathlib.Tactic.Linarith
import Mathlib

/-!
# Franklin Involution → Euler Pentagonal Number Theorem (Combinatorial)

The final assembly: use the Franklin involution (Ch04Franklin infrastructure) to prove
the combinatorial form of Euler's pentagonal number theorem.

## Strategy

A strict partition of n is a subset S ⊆ {1,...,n} with ∑ S = n.
The signed count is ∑_{S : strict partition of n} (-1)^|S|.
Franklin's involution pairs most S with a partner of opposite sign.
The only unpaired partitions are the pentagonal fixed shapes
{k, k+1, ..., 2k-1} (weight = k(3k-1)/2) and {k+1, k+2, ..., 2k}
(weight = k(3k+1)/2). These contribute (-1)^k each.

Result: ∑ (-1)^|S| = (-1)^k if n = k(3k±1)/2, else 0.
-/

open QseriesFormalization PartI Ch04Franklin

open QseriesFormalization QseriesFormalization.PartI QseriesFormalization.PartI.Ch04Franklin

-- Sanity: pentagonal numbers are 0, 1, 2, 5, 7, 12, 15, 22, 26, ...
-- Signs:                          +1, -1, -1, +1, +1, -1, -1, +1, +1, ...
-- Signed strict partition counts
/-! ### Franklin involution on Finset Nat

Standard definition (Andrews, *The Theory of Partitions*):
Given strict partition S = {λ₁ > λ₂ > ... > λₖ} (distinct positive integers):
- σ = S.min' (smallest part)
- t = max{j : S.max', S.max'-1, ..., S.max'-j+1 all ∈ S} (top staircase length)

If σ < t, or σ = t and σ ≤ S.max' - σ (bottom doesn't overlap top after shift):
  → Remove σ; add 1 to each of the top σ parts. (Card decreases by 1.)
If σ > t, or σ = t and σ > S.max' - σ:
  → Subtract 1 from each of the top t parts; add new part t. (Card increases by 1.)
Fixed points: σ = t with specific overlap = pentagonal shapes. -/

-- Sanity: topStaircase
-- Sanity: franklinInv involution
-- {3, 1} (wt 4): σ=1, t=1, σ≤t. σ=t, σ∈topParts? topParts={3}, 1∉{3}. No.
-- Move bottom to top: result = {4}. Card 2→1.
/-! ### Verified instances of the pentagonal number theorem

While the general proof (via Franklin involution) is developed over multiple
sessions, we verify the theorem for all n ≤ 22 via native_decide. -/

/-! ### Helper lemmas for Franklin involution proofs -/

open Finset

/-! ## takeWhile infrastructure -/

/-! ## topStaircase properties -/

/-! ## Derived topStaircase utilities -/

/-! ## Equational lemmas: fixed-point cases -/

/-! ## Equational lemmas: non-fixed cases -/

/-! ### Key properties of franklinInv -/

open Finset

-- Verified: involution on all strict partitions of weight ≤ 7

/-! ### Fixed-point characterization and pentagonal number helpers -/

open Finset

-- Forward: fixed → Type A or Type B

theorem QseriesFormalization.PartI.Ch04Franklin.fixed_implies_pentagonal {S : Finset Nat} (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x) (hfixed : franklinInv S = S) :
    (∃ k, k ≥ 1 ∧ (S = Finset.Icc k (2 * k - 1) ∨ S = Finset.Icc (k + 1) (2 * k))) := by sorry
