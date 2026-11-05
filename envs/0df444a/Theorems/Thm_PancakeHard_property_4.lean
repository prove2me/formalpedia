-- Prove2me | Theorems.Thm_PancakeHard_property_4
-- name    : PancakeHard.property_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T07:02:18.576009+00:00
-- url     : https://prove2.me/theorems/bcea71f7-3399-4eba-a4d8-920b61d306c5
-- title:
--   Property 4 — dock gadget: $\langle\star\mathcal I_q^{p+1},X,D,Y\rangle\Longrightarrow\langle X,\mathcal I^{p-1}_{q+2},Y\rangle$
-- statement:
--   Let $p<q$, $D=Dock(p,q)$, and let $X$, $Y$ be any sequences. Then
--   $$\langle\star\mathcal I_q^{p+1},X,D,Y\rangle\Longrightarrow\langle X,\mathcal I^{p-1}_{q+2},Y\rangle .$$
--
--   A block $\langle q,\dots,p+1\rangle$ at the head is thus stored at the dock without touching the rest of the stack.
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
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.1.1, p.4, Property 4

import Mathlib
import Definitions.Def_PancakeHard_Dock

set_option autoImplicit false

namespace PancakeHard

/-- **Property 4** (dock gadget; Bulteau, Fertin, Rusu, *Pancake Flipping Is Hard*, arXiv:1111.0434v2, §3.1.1, p.4): "Let p and q be any integers with p < q,
D = Dock(p, q), and X and Y be any sequences. We have ⟨⋆𝓘^{p+1}_q, X, D, Y⟩ ⟹ ⟨X, 𝓘^{p−1}_{q+2}, Y⟩."

**Formalization Note** "Any sequences" are read with the paper's convention (p.2; p.13: "all sequences considered are permutations"): the left-hand sequence is a stack, a permutation of `⟦1 ; n⟧` with `n` its length; `X`, `Y`, `Z` may be empty. The head is the first list entry. `⋆𝓘^{p+1}_q` is `(interval (p + 1) q).reverse`. `p, q` are natural numbers; the stack
hypothesis forces `p − 1 ≥ 1`, so the truncated `p − 1` is the paper's. -/
theorem property_4 (p q : ℕ) (X Y : List ℕ) (hpq : p < q)
    (hS : IsStack ((interval (p + 1) q).reverse ++ X ++ Dock p q ++ Y)) :
    LeadsTo ((interval (p + 1) q).reverse ++ X ++ Dock p q ++ Y)
      {X ++ interval (p - 1) (q + 2) ++ Y} := by sorry

end PancakeHard
