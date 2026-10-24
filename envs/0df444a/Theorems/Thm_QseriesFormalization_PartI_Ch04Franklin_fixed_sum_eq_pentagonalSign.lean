-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04Franklin_fixed_sum_eq_pentagonalSign
-- name    : QseriesFormalization.PartI.Ch04Franklin.fixed_sum_eq_pentagonalSign
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:25:10.2463+00:00
-- url     : https://prove2.me/theorems/5232768f-dd62-4199-bbad-e7131973256a
-- title:
--   Signed count of Franklin-fixed strict partitions equals the pentagonal sign
-- statement:
--   For every natural number $n$, summing $(-1)^{|S|}$ over those strict partitions $S$ of $n$ (finite sets of distinct positive integers with sum $n$) that are fixed by Franklin's involution gives the pentagonal sign:
--   $$\sum_{\substack{S\in \mathrm{StrictPartitionSet}(n)\\ \mathrm{franklinInv}(S)=S}}(-1)^{|S|}=\mathrm{pentagonalSign}(n).$$
--   Here $\mathrm{pentagonalSign}(n)=(-1)^k$ if $n=k(3k\mp1)/2$ is a generalized pentagonal number with index $k$, and $0$ otherwise. This is the last step before Euler's pentagonal number theorem in its combinatorial form.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 5. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter05_Franklin.lean#L1303-L1357

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

-- Backward: pentagonal → fixed

/-! ### Pentagonal number arithmetic -/

open Finset

-- Gauss sum helpers

-- Assembly helpers

/-! ### Sign cancellation and final assembly -/

open Finset

theorem QseriesFormalization.PartI.Ch04Franklin.fixed_sum_eq_pentagonalSign (n : Nat) :
    ∑ S ∈ (StrictPartitionSet n).filter (fun S => franklinInv S = S), (-1:Int)^S.card =
    pentagonalSign n := by sorry
