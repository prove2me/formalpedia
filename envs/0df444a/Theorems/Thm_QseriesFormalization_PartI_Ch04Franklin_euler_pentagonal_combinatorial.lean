-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04Franklin_euler_pentagonal_combinatorial
-- name    : QseriesFormalization.PartI.Ch04Franklin.euler_pentagonal_combinatorial
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:23:43.382658+00:00
-- url     : https://prove2.me/theorems/13673b29-50ff-4f7d-a620-f9cb6f681516
-- title:
--   Euler's pentagonal number theorem, combinatorial form
-- statement:
--   For every natural number $n$, the signed number of partitions of $n$ into distinct positive parts equals the pentagonal sign:
--   $$\sum_{S\ \text{strict partition of } n}(-1)^{|S|}=\mathrm{pentagonalSign}(n),$$
--   where $|S|$ is the number of parts and $\mathrm{pentagonalSign}(n)=(-1)^k$ if $n=k(3k\mp1)/2$ for some $k\ge0$ (generalized pentagonal number) and $0$ otherwise. Equivalently the coefficient of $q^n$ in $\prod_{i\ge1}(1-q^i)$ is the pentagonal sign.
--
--   This is the Franklin-involution proof of Euler's pentagonal number theorem; the Lean statement is the general theorem, for all $n$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 5. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter05_Franklin.lean#L1361-L1376

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

theorem QseriesFormalization.PartI.Ch04Franklin.euler_pentagonal_combinatorial (n : Nat) :
    signedStrictPartitionCount n = pentagonalSign n := by sorry
