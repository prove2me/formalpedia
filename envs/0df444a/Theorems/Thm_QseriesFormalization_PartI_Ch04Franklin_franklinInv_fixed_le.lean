-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04Franklin_franklinInv_fixed_le
-- name    : QseriesFormalization.PartI.Ch04Franklin.franklinInv_fixed_le
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:25:48.4592+00:00
-- url     : https://prove2.me/theorems/e86a4315-072d-4571-b1e0-1c782e35014c
-- title:
--   Franklin's involution fixes the sets in the exceptional case
-- statement:
--   Let $S$ be a nonempty finite set of naturals, with minimum $\sigma=\min S$, maximum $m=\max S$, and let $t=\mathrm{topStaircase}(S)$ be the length of the run $m,m-1,\dots,m-t+1$ of consecutive elements of $S$ at the top. Assume $\sigma\le t$ and in fact $\sigma=t$, together with either $m-t+1=\sigma$ or $\sigma\in\{m-i: 0\le i<t\}$. Then Franklin's involution fixes $S$:
--   $$\mathrm{franklinInv}(S)=S .$$
--   This is one of the case lemmas in the combinatorial proof of Euler's pentagonal number theorem; the fixed points are exactly the partitions of pentagonal shape.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 5. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter05_Franklin.lean#L287-L304

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

theorem QseriesFormalization.PartI.Ch04Franklin.franklinInv_fixed_le {S : Finset Nat} (hne : S.Nonempty)
    (h_le : S.min' hne ≤ topStaircase S)
    (h_fixed : S.min' hne = topStaircase S ∧
      (S.max' hne - topStaircase S + 1 = S.min' hne ∨
       S.min' hne ∈ (Finset.range (topStaircase S)).image (S.max' hne - ·))) :
    franklinInv S = S := by sorry
