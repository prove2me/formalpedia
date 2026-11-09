-- Prove2me | Theorems.Thm_PancakeHard_property_6
-- name    : PancakeHard.property_6
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T07:01:52.275536+00:00
-- url     : https://prove2.me/theorems/c252e1b0-44d2-4dfe-ad8f-b04cb69427f3
-- title:
--   Property 6 — hook gadget (a. take, b. put, c. release)
-- statement:
--   Let $(take,put,G,H)=Hook(p)$ and let $X$, $Y$, $Z$ be any sequences. Then
--
--   1. $\langle take,X,G,Y,H,Z\rangle\Longrightarrow\langle Y,G',\star X,H',Z\rangle$;
--   2. $\langle put,X,G',\star Y,H',Z\rangle\Longrightarrow\langle Y,G'',X,H'',Z\rangle$;
--   3. $\langle G'',X,H'',Y\rangle\Longrightarrow\langle X,\star\mathcal I^{p+1}_{p+12},Y\rangle$.
--
--   The hook brings the delimited sequence to the head and stores it back.
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
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.1.3, p.7, Property 6

import Mathlib
import Definitions.Def_PancakeHard_Hook

set_option autoImplicit false

namespace PancakeHard

/-- **Property 6** (hook gadget; Bulteau, Fertin, Rusu, *Pancake Flipping Is Hard*, arXiv:1111.0434v2, §3.1.3, p.7): "Let p be an integer, (take, put, G, H) = Hook(p),
and X, Y and Z be any sequences. We have
a. ⟨take, X, G, Y, H, Z⟩ ⟹ ⟨Y, G′, ⋆X, H′, Z⟩
b. ⟨put, X, G′, ⋆Y, H′, Z⟩ ⟹ ⟨Y, G″, X, H″, Z⟩
c. ⟨G″, X, H″, Y⟩ ⟹ ⟨X, ⋆𝓘^{p+1}_{p+12}, Y⟩"

**Formalization Note** "Any sequences" are read with the paper's convention (p.2; p.13: "all sequences considered are permutations"): the left-hand sequence is a stack, a permutation of `⟦1 ; n⟧` with `n` its length; `X`, `Y`, `Z` may be empty. The head is the first list entry. `⋆X` is `X.reverse`; `p` is a natural number. -/
theorem property_6 (p : ℕ) (X Y Z : List ℕ) :
    (IsStack (hookTake p :: X ++ hookG p ++ Y ++ hookH p ++ Z) →
      LeadsTo (hookTake p :: X ++ hookG p ++ Y ++ hookH p ++ Z)
        {Y ++ hookG' p ++ X.reverse ++ hookH' p ++ Z}) ∧
    (IsStack (hookPut p :: X ++ hookG' p ++ Y.reverse ++ hookH' p ++ Z) →
      LeadsTo (hookPut p :: X ++ hookG' p ++ Y.reverse ++ hookH' p ++ Z)
        {Y ++ hookG'' p ++ X ++ hookH'' p ++ Z}) ∧
    (IsStack (hookG'' p ++ X ++ hookH'' p ++ Y) →
      LeadsTo (hookG'' p ++ X ++ hookH'' p ++ Y)
        {X ++ (interval (p + 1) (p + 12)).reverse ++ Y}) := by sorry

end PancakeHard
