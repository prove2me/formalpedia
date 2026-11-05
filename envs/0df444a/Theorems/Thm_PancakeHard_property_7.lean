-- Prove2me | Theorems.Thm_PancakeHard_property_7
-- name    : PancakeHard.property_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:01:55.250831+00:00
-- url     : https://prove2.me/theorems/bfdddbcd-39f8-4a90-9916-87f83310fdfe
-- title:
--   Property 7 — fork gadget (a. choice between $X$ and $\star X$, b.–c. release)
-- statement:
--   Let $(E,F)=Fork(p)$ and let $X$, $Y$ be any sequences. Then
--
--   1. $\langle E,X,F,Y\rangle\Longrightarrow\{\langle X,F^1,Y\rangle,\ \langle\star X,F^2,Y\rangle\}$;
--   2. $\langle F^1,Y\rangle\Longrightarrow\langle\star\mathcal I^{p+1}_{p+15},Y\rangle$;
--   3. $\langle F^2,Y\rangle\Longrightarrow\langle\star\mathcal I^{p+1}_{p+15},Y\rangle$.
--
--   Every efficient path through a fork chooses whether $X$ or its reversal reaches the head first.
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
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.1.4, p.7, Property 7

import Mathlib
import Definitions.Def_PancakeHard_Fork

set_option autoImplicit false

namespace PancakeHard

/-- **Property 7** (fork gadget; Bulteau, Fertin, Rusu, *Pancake Flipping Is Hard*, arXiv:1111.0434v2, §3.1.4, p.7): "Let p be an integer, (E, F) = Fork(p), and X, Y be
any sequences. We have
a. ⟨E, X, F, Y⟩ ⟹ {⟨X, F¹, Y⟩, ⟨⋆X, F², Y⟩}
b. ⟨F¹, Y⟩ ⟹ ⟨⋆𝓘^{p+1}_{p+15}, Y⟩
c. ⟨F², Y⟩ ⟹ ⟨⋆𝓘^{p+1}_{p+15}, Y⟩"

**Formalization Note** "Any sequences" are read with the paper's convention (p.2; p.13: "all sequences considered are permutations"): the left-hand sequence is a stack, a permutation of `⟦1 ; n⟧` with `n` its length; `X`, `Y`, `Z` may be empty. The head is the first list entry. `p` is a natural number. -/
theorem property_7 (p : ℕ) (X Y : List ℕ) :
    (IsStack (forkE p ++ X ++ forkF p ++ Y) →
      LeadsTo (forkE p ++ X ++ forkF p ++ Y)
        {X ++ forkF1 p ++ Y, X.reverse ++ forkF2 p ++ Y}) ∧
    (IsStack (forkF1 p ++ Y) →
      LeadsTo (forkF1 p ++ Y) {(interval (p + 1) (p + 15)).reverse ++ Y}) ∧
    (IsStack (forkF2 p ++ Y) →
      LeadsTo (forkF2 p ++ Y) {(interval (p + 1) (p + 15)).reverse ++ Y}) := by sorry

end PancakeHard
