-- Prove2me | Theorems.Thm_PancakeHard_property_8
-- name    : PancakeHard.property_8
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T07:03:03.476534+00:00
-- url     : https://prove2.me/theorems/81bea6f4-985f-46d0-aa78-1c2c42c60cb2
-- title:
--   Property 8 — literals gadget (a. opening lock $i$, b. testing an open lock, c. testing a closed lock)
-- statement:
--   Let $(key_1,\dots,key_m,test_1,\dots,test_m,\Lambda)=Literals(p,m)$, let $O$, $I$ be disjoint subsets of $\llbracket 1;m\rrbracket$, and let $X$ be any sequence. Then
--
--   1. for every $i\in\llbracket 1;m\rrbracket-O-I$: $\langle key_i,X,\Lambda^O_I\rangle\Longrightarrow\langle X,\Lambda^{O\cup\{i\}}_I\rangle$;
--   2. for every $i\in O$: $\langle test_i,X,\Lambda^O_I\rangle\Longrightarrow\langle X,\Lambda^{O-\{i\}}_{I\cup\{i\}}\rangle$;
--   3. for every $i\in\llbracket 1;m\rrbracket-O$: $\langle test_i,X,\Lambda^O_I\rangle\to\bot$.
--
--   For $i\in I$ in part 3 the sequence contains $test_i$ twice and is not a permutation, as the paper observes; the hypothesis that it is a permutation then excludes the case.
--
--
--   **Formalization Note** Sequences are lists of natural numbers with the head first; the statement assumes, as the paper does throughout (p.2, p.13), that the left-hand sequence is a permutation of $\llbracket 1 ; n\rrbracket$, where $n$ is its length. The context sequences may be empty.
--
--   Differences from the source:
--   - encoding: a sequence ⟨x₁, …, xₙ⟩ with head element x₁ → a list of natural numbers whose first entry is the head; reason: Lean convention; same instances
--   - reading: X, Y (, Z) are any sequences → the left-hand sequence is a permutation of ⟦1 ; n⟧, n its length (IsStack); X, Y, Z stay arbitrary and may be empty; reason: p.2: input sequences are permutations of ⟦1 ; n⟧; p.13: all sequences considered are permutations
--   - encoding: p (and q) are integers → natural numbers; reason: every gadget contains p + 1 (a dock p − 1) and a stack has entries ≥ 1, so a negative offset gives no stack; same instances
--   - encoding: a path is a series of flips, which goes through T → the list of visited sequences, consecutive ones related by an efficient flip; T is visited if it is in the list, endpoints included; reason: a flip sequence and its visited sequences determine each other on permutations; p.4 (Lemma 13) and Property 2 count endpoints
--   - encoding: O, I disjoint subsets of ⟦1 ; m⟧ → Finset ℕ with O, I ⊆ Icc 1 m and Disjoint O I; reason: same instances
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.2.1, p.9, Property 8

import Mathlib
import Definitions.Def_PancakeHard_Literals

set_option autoImplicit false

namespace PancakeHard

/-- **Property 8** (literals gadget; Bulteau, Fertin, Rusu, *Pancake Flipping Is Hard*, arXiv:1111.0434v2, §3.2.1, p.9): "Let p and m be two integers,
(key₁, …, key_m, test₁, …, test_m, Λ) = Literals(p, m), O and I be two disjoint subsets of ⟦1 ; m⟧, and
X be any sequence. We have
a. ∀i ∈ ⟦1 ; m⟧ − O − I, ⟨keyᵢ, X, Λ^O_I⟩ ⟹ ⟨X, Λ^{O∪{i}}_I⟩
b. ∀i ∈ O, ⟨testᵢ, X, Λ^O_I⟩ ⟹ ⟨X, Λ^{O−{i}}_{I∪{i}}⟩
c. ∀i ∈ ⟦1 ; m⟧ − O, ⟨testᵢ, X, Λ^O_I⟩ → ⊥"

**Formalization Note** "Any sequences" are read with the paper's convention (p.2; p.13: "all sequences considered are permutations"): the left-hand sequence is a stack, a permutation of `⟦1 ; n⟧` with `n` its length; `X`, `Y`, `Z` may be empty. The head is the first list entry. For `i ∈ I` in part c. the left-hand sequence contains `testᵢ` twice, so the stack
hypothesis fails, as the paper's proof notes ("not a valid sequence"). -/
theorem property_8 (p m : ℕ) (O I : Finset ℕ) (X : List ℕ) (hO : O ⊆ Finset.Icc 1 m)
    (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I) :
    (∀ i ∈ Finset.Icc 1 m, i ∉ O → i ∉ I →
      IsStack (litKey p i :: X ++ literals p m O I) →
      LeadsTo (litKey p i :: X ++ literals p m O I) {X ++ literals p m (insert i O) I}) ∧
    (∀ i ∈ O,
      IsStack (litTest p i :: X ++ literals p m O I) →
      LeadsTo (litTest p i :: X ++ literals p m O I)
        {X ++ literals p m (O.erase i) (insert i I)}) ∧
    (∀ i ∈ Finset.Icc 1 m, i ∉ O →
      IsStack (litTest p i :: X ++ literals p m O I) →
      IsDeadlock (litTest p i :: X ++ literals p m O I)) := by sorry

end PancakeHard
