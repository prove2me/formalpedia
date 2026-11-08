-- Prove2me | Theorems.Thm_PancakeHard_property_5
-- name    : PancakeHard.property_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T07:02:04.27718+00:00
-- url     : https://prove2.me/theorems/2956dde6-cb9a-4627-bfd0-048cc0c348e8
-- title:
--   Property 5 — lock gadget (a. opening, b. testing an open lock, c. testing a closed lock is a deadlock)
-- statement:
--   Let $(key,test,L)=Lock(p)$ and let $X$, $Y$ be any sequences. Then
--
--   1. $\langle key,X,L,Y\rangle\Longrightarrow\langle X,L^o,Y\rangle$;
--   2. $\langle test,X,L^o,Y\rangle\Longrightarrow\langle X,\mathcal I^{p+1}_{p+12},Y\rangle$;
--   3. $\langle test,X,L,Y\rangle\to\bot$ (a deadlock).
--
--   A key opens its lock, and a test passes exactly when the lock is open.
--
--
--   **Formalization Note** Sequences are lists of natural numbers with the head first; the statement assumes, as the paper does throughout (p.2, p.13), that the left-hand sequence is a permutation of $\llbracket 1 ; n\rrbracket$, where $n$ is its length. The context sequences may be empty.
--
--   Differences from the source:
--   - encoding: a sequence ⟨x₁, …, xₙ⟩ with head element x₁ → a list of natural numbers whose first entry is the head; reason: Lean convention; same instances
--   - reading: X, Y (, Z) are any sequences → the left-hand sequence is a permutation of ⟦1 ; n⟧, n its length (IsStack); X, Y, Z stay arbitrary and may be empty; reason: p.2: input sequences are permutations of ⟦1 ; n⟧; p.13: all sequences considered are permutations
--   - encoding: p (and q) are integers → natural numbers; reason: every gadget contains p + 1 (a dock p − 1) and a stack has entries ≥ 1, so a negative offset gives no stack; same instances
--   - encoding: a path is a series of flips, which goes through T → the list of visited sequences, consecutive ones related by an efficient flip; T is visited if it is in the list, endpoints included; reason: a flip sequence and its visited sequences determine each other on permutations; p.4 (Lemma 13) and Property 2 count endpoints
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.1.2, p.5, Property 5

import Mathlib
import Definitions.Def_PancakeHard_Lock

set_option autoImplicit false

namespace PancakeHard

/-- **Property 5** (lock gadget; Bulteau, Fertin, Rusu, *Pancake Flipping Is Hard*, arXiv:1111.0434v2, §3.1.2, p.5): "Let p be any integer, (key, test, L) = Lock(p),
and X and Y be any sequences. We have
a. ⟨key, X, L, Y⟩ ⟹ ⟨X, Lᵒ, Y⟩
b. ⟨test, X, Lᵒ, Y⟩ ⟹ ⟨X, 𝓘^{p+1}_{p+12}, Y⟩
c. ⟨test, X, L, Y⟩ → ⊥"

**Formalization Note** "Any sequences" are read with the paper's convention (p.2; p.13: "all sequences considered are permutations"): the left-hand sequence is a stack, a permutation of `⟦1 ; n⟧` with `n` its length; `X`, `Y`, `Z` may be empty. The head is the first list entry. `p` is a natural number (a stack has entries `≥ 1`, so `p + 1 ≥ 1` excludes nothing). -/
theorem property_5 (p : ℕ) (X Y : List ℕ) :
    (IsStack (lockKey p :: X ++ lockSeq p ++ Y) →
      LeadsTo (lockKey p :: X ++ lockSeq p ++ Y) {X ++ lockOpen p ++ Y}) ∧
    (IsStack (lockTest p :: X ++ lockOpen p ++ Y) →
      LeadsTo (lockTest p :: X ++ lockOpen p ++ Y) {X ++ interval (p + 1) (p + 12) ++ Y}) ∧
    (IsStack (lockTest p :: X ++ lockSeq p ++ Y) →
      IsDeadlock (lockTest p :: X ++ lockSeq p ++ Y)) := by sorry

end PancakeHard
