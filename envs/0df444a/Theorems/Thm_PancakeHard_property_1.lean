-- Prove2me | Theorems.Thm_PancakeHard_property_1
-- name    : PancakeHard.property_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T07:01:22.709522+00:00
-- url     : https://prove2.me/theorems/27cf87f2-6b3c-4d4d-b15a-57ba290a644c
-- title:
--   Property 1 — one flip changes $d_b$ by $-1$, $0$ or $1$
-- statement:
--   Let $S$ be a permutation of $\llbracket 1;n\rrbracket$ and let $S'$ be obtained from $S$ by one flip (of a length $1\le r\le n$). Then
--   $$d_b(S')-d_b(S)\in\{-1,0,1\}.$$
--
--   Consequently a stack with $d_b(S)$ breakpoints needs at least $d_b(S)$ flips to be sorted, and the efficient flips are exactly those that achieve this bound one step at a time.
--
--   Differences from the source:
--   - encoding: a sequence ⟨x₁, …, xₙ⟩ with head element x₁ → a list of natural numbers whose first entry is the head; reason: Lean convention; same instances
--   - reading: the sequences S, S′ of Property 1 → S is a permutation of ⟦1 ; n⟧, n its length (IsStack); reason: p.2: input sequences are permutations of ⟦1 ; n⟧; a sequence reached by flips from S is one too
--   - encoding: d_b(S′) − d_b(S) → the difference of the two counts computed in ℤ; reason: avoids natural-number subtraction; same value
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §2, p.3, Property 1

import Mathlib
import Definitions.Def_PancakeHard_Basic

set_option autoImplicit false

namespace PancakeHard

/-- **Property 1** (Bulteau, Fertin, Rusu, *Pancake Flipping Is Hard*, arXiv:1111.0434v2, §2, p.3): "Given a sequence S′ obtained from a sequence S by performing one
flip, we have d_b(S′) − d_b(S) ∈ {−1, 0, 1}."

**Formalization Note** `S` is a stack (p.2); a flip has length `1 ≤ r ≤ n` (`IsFlip`). The difference
is taken in `ℤ`. -/
theorem property_1 (S S' : List ℕ) (hS : IsStack S) (h : IsFlip S S') :
    (breakpoints S' : ℤ) - breakpoints S ∈ ({-1, 0, 1} : Set ℤ) := by sorry

end PancakeHard
