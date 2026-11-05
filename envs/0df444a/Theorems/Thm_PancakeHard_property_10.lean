-- Prove2me | Theorems.Thm_PancakeHard_property_10
-- name    : PancakeHard.property_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:03:57.082934+00:00
-- url     : https://prove2.me/theorems/6cc0776d-ec78-4751-810c-65b4fe874a96
-- title:
--   Property 10 — clause gadget: $\langle\gamma,X,\Gamma,Y,\Lambda^O_I\rangle\Longrightarrow\mathbb T$ with $0$ to $3$ outcomes
-- statement:
--   Let $(\gamma,\Gamma,\Delta)=Clause(a,b,c,p)$ for pairwise distinct $a,b,c\in\llbracket 1;m\rrbracket$, with $\Lambda^O_I$ from $Literals(p_\Lambda,m)$. Let $X$, $Y$ be any sequences and $O$, $I$ disjoint subsets of $\llbracket 1;m\rrbracket$. Then
--   $$\langle\gamma,X,\Gamma,Y,\Lambda^O_I\rangle\Longrightarrow\mathbb T,$$
--   where $\mathbb T$ contains from $0$ to $3$ sequences and is defined by
--   $$\langle X,\Gamma^1,Y,\Lambda^{O-\{a\}}_{I\cup\{a\}}\rangle\in\mathbb T\iff a\in O,\quad\langle X,\Gamma^2,Y,\Lambda^{O-\{b\}}_{I\cup\{b\}}\rangle\in\mathbb T\iff b\in O,\quad\langle X,\Gamma^3,Y,\Lambda^{O-\{c\}}_{I\cup\{c\}}\rangle\in\mathbb T\iff c\in O .$$
--
--   Every efficient path through a clause gadget tests one open lock among those of its three literals; if none is open, $\mathbb T=\emptyset$ and the sequence is not efficiently sortable.
--
--
--   **Formalization Note** Sequences are lists of natural numbers with the head first; the statement assumes, as the paper does throughout (p.2, p.13), that the left-hand sequence is a permutation of $\llbracket 1 ; n\rrbracket$, where $n$ is its length. The context sequences may be empty.
--
--   Differences from the source:
--   - encoding: a sequence ⟨x₁, …, xₙ⟩ with head element x₁ → a list of natural numbers whose first entry is the head; reason: Lean convention; same instances
--   - reading: X, Y (, Z) are any sequences → the left-hand sequence is a permutation of ⟦1 ; n⟧, n its length (IsStack); X, Y, Z stay arbitrary and may be empty; reason: p.2: input sequences are permutations of ⟦1 ; n⟧; p.13: all sequences considered are permutations
--   - encoding: p is an integer → p : ℤ with -2 ≤ p, offsets written (p + c).toNat; p_Λ and m are natural numbers; reason: the least entry of Γ is p + 3 and a stack has entries ≥ 1, so p < −2 gives no stack; p = −2 and p = −1 do occur; for p ≥ −2 each (p + c).toNat is p + c; a Literals gadget with m ≥ 1 contains p_Λ + 1; same instances
--   - encoding: a path is a series of flips, which goes through T → the list of visited sequences, consecutive ones related by an efficient flip; T is visited if it is in the list, endpoints included; reason: a flip sequence and its visited sequences determine each other on permutations; p.4 (Lemma 13) and Property 2 count endpoints
--   - encoding: O, I disjoint subsets of ⟦1 ; m⟧ → Finset ℕ with O, I ⊆ Icc 1 m and Disjoint O I; reason: same instances
--   - encoding: 𝕋 defined by three membership conditions → the set of the listed sequences whose condition holds; reason: Γ¹, Γ², Γ³ are distinct lists, so the set is exactly the paper's
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.2.3, p.17, Property 10

import Mathlib
import Definitions.Def_PancakeHard_Clause

set_option autoImplicit false

namespace PancakeHard

/-- **Property 10** (clause gadget; Bulteau, Fertin, Rusu, *Pancake Flipping Is Hard*, arXiv:1111.0434v2, §3.2.3, p.17): "Let X and Y be any sequences, and O, I be
two disjoint subsets of ⟦1 ; m⟧. We have ⟨γ, X, Γ, Y, Λ^O_I⟩ ⟹ 𝕋 where 𝕋 contains from 0 to 3
sequences, and is defined by:
⟨X, Γ¹, Y, Λ^{O−{a}}_{I∪{a}}⟩ ∈ 𝕋 iff a ∈ O
⟨X, Γ², Y, Λ^{O−{b}}_{I∪{b}}⟩ ∈ 𝕋 iff b ∈ O
⟨X, Γ³, Y, Λ^{O−{c}}_{I∪{c}}⟩ ∈ 𝕋 iff c ∈ O"
for `(γ, Γ, Δ) = Clause(a, b, c, p)` with `a, b, c ∈ ⟦1 ; m⟧` pairwise distinct (Definition 7, p.16) and
`Λ^O_I` that of `Literals(p_Λ, m)` (p.13).

**Formalization Note** "Any sequences" are read with the paper's convention (p.2; p.13: "all sequences considered are permutations"): the left-hand sequence is a stack, a permutation of `⟦1 ; n⟧` with `n` its length; `X`, `Y`, `Z` may be empty. The head is the first list entry. `𝕋` is the set of the listed sequences whose condition holds; it may be empty. `p` is an integer, as on the page: `p = −2` and `p = −1` occur here (the least entry of `Γ` is
`p + 3`); `-2 ≤ p` excludes no instance, since below it `Γ` has a nonpositive entry, and it makes each
`(p + c).toNat` the page's `p + c`. -/
theorem property_10 (pΛ m : ℕ) (p : ℤ) (hp : -2 ≤ p) (a b c : ℕ) (O I : Finset ℕ) (X Y : List ℕ)
    (ha : a ∈ Finset.Icc 1 m) (hb : b ∈ Finset.Icc 1 m) (hc : c ∈ Finset.Icc 1 m)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hO : O ⊆ Finset.Icc 1 m)
    (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hS : IsStack (clauseGamma p :: X ++ clauseΓ pΛ a b c p ++ Y ++ literals pΛ m O I)) :
    LeadsTo (clauseGamma p :: X ++ clauseΓ pΛ a b c p ++ Y ++ literals pΛ m O I)
      {T | (a ∈ O ∧ T = X ++ clauseΓ1 pΛ b c p ++ Y ++ literals pΛ m (O.erase a) (insert a I)) ∨
        (b ∈ O ∧ T = X ++ clauseΓ2 pΛ a c p ++ Y ++ literals pΛ m (O.erase b) (insert b I)) ∨
        (c ∈ O ∧ T = X ++ clauseΓ3 pΛ a b p ++ Y ++ literals pΛ m (O.erase c) (insert c I))} := by sorry

end PancakeHard
