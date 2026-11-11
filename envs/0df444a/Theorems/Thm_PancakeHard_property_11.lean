-- Prove2me | Theorems.Thm_PancakeHard_property_11
-- name    : PancakeHard.property_11
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T07:03:26.188199+00:00
-- url     : https://prove2.me/theorems/3cbd906b-82f5-4e05-89af-ae0a0c2fd190
-- title:
--   Property 11 — clause gadget completion (a. from $\Gamma^1$, b. from $\Gamma^2$, c. from $\Gamma^3$)
-- statement:
--   Let $(\gamma,\Gamma,\Delta)=Clause(a,b,c,p)$ for pairwise distinct $a,b,c\in\llbracket 1;m\rrbracket$, with $\Lambda^O_I$ from $Literals(p_\Lambda,m)$. Let $Y$, $Z$ be any sequences and $O$, $I$ disjoint subsets of $\llbracket 1;m\rrbracket$. Then
--
--   1. if $b,c\in O$: $\langle\Gamma^1,Y,\Delta,Z,\Lambda^O_I\rangle\Longrightarrow\langle Y,\mathcal I^{p+1}_{p+62},Z,\Lambda^{O-\{b,c\}}_{I\cup\{b,c\}}\rangle$;
--   2. if $a,c\in O$: $\langle\Gamma^2,Y,\Delta,Z,\Lambda^O_I\rangle\Longrightarrow\langle Y,\mathcal I^{p+1}_{p+62},Z,\Lambda^{O-\{a,c\}}_{I\cup\{a,c\}}\rangle$;
--   3. if $a,b\in O$: $\langle\Gamma^3,Y,\Delta,Z,\Lambda^O_I\rangle\Longrightarrow\langle Y,\mathcal I^{p+1}_{p+62},Z,\Lambda^{O-\{a,b\}}_{I\cup\{a,b\}}\rangle$.
--
--   Once one literal of a clause has been tested, the clause gadget can be cleared provided the two remaining locks are open.
--
--
--   **Formalization Note** Sequences are lists of natural numbers with the head first; the statement assumes, as the paper does throughout (p.2, p.13), that the left-hand sequence is a permutation of $\llbracket 1 ; n\rrbracket$, where $n$ is its length. The context sequences may be empty.
--
--   Differences from the source:
--   - encoding: a sequence ⟨x₁, …, xₙ⟩ with head element x₁ → a list of natural numbers whose first entry is the head; reason: Lean convention; same instances
--   - reading: X, Y (, Z) are any sequences → the left-hand sequence is a permutation of ⟦1 ; n⟧, n its length (IsStack); X, Y, Z stay arbitrary and may be empty; reason: p.2: input sequences are permutations of ⟦1 ; n⟧; p.13: all sequences considered are permutations
--   - encoding: p is an integer → p : ℤ with -2 ≤ p, offsets written (p + c).toNat; p_Λ and m are natural numbers; reason: the least entry of Γ¹, Γ², Γ³ is p + 3 and Δ contains p + 1, so the stack hypothesis gives p ≥ 0; -2 ≤ p excludes no instance and each (p + c).toNat is p + c; a Literals gadget with m ≥ 1 contains p_Λ + 1; same instances
--   - encoding: a path is a series of flips, which goes through T → the list of visited sequences, consecutive ones related by an efficient flip; T is visited if it is in the list, endpoints included; reason: a flip sequence and its visited sequences determine each other on permutations; p.4 (Lemma 13) and Property 2 count endpoints
--   - encoding: O, I disjoint subsets of ⟦1 ; m⟧ → Finset ℕ with O, I ⊆ Icc 1 m and Disjoint O I; reason: same instances
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.2.3, p.18, Property 11

import Mathlib
import Definitions.Def_PancakeHard_Clause

set_option autoImplicit false

namespace PancakeHard

/-- **Property 11** (clause gadget; Bulteau, Fertin, Rusu, *Pancake Flipping Is Hard*, arXiv:1111.0434v2, §3.2.3, p.18): "Let Y and Z be any sequences, and O, I be two
disjoint subsets of ⟦1 ; m⟧. We have
a. If b, c ∈ O, then ⟨Γ¹, Y, Δ, Z, Λ^O_I⟩ ⟹ ⟨Y, 𝓘^{p+1}_{p+62}, Z, Λ^{O−{b,c}}_{I∪{b,c}}⟩
b. If a, c ∈ O, then ⟨Γ², Y, Δ, Z, Λ^O_I⟩ ⟹ ⟨Y, 𝓘^{p+1}_{p+62}, Z, Λ^{O−{a,c}}_{I∪{a,c}}⟩
c. If a, b ∈ O, then ⟨Γ³, Y, Δ, Z, Λ^O_I⟩ ⟹ ⟨Y, 𝓘^{p+1}_{p+62}, Z, Λ^{O−{a,b}}_{I∪{a,b}}⟩"
for `(γ, Γ, Δ) = Clause(a, b, c, p)` with `a, b, c ∈ ⟦1 ; m⟧` pairwise distinct (Definition 7, p.16) and
`Λ^O_I` that of `Literals(p_Λ, m)` (p.13).

**Formalization Note** "Any sequences" are read with the paper's convention (p.2; p.13: "all sequences considered are permutations"): the left-hand sequence is a stack, a permutation of `⟦1 ; n⟧` with `n` its length; `X`, `Y`, `Z` may be empty. The head is the first list entry. `p` is an integer, as on the page; `-2 ≤ p` excludes no instance, since below it `Γ¹` has a nonpositive entry, and `Δ` contains
`p + 1`, so the stack hypothesis gives `p ≥ 0`. -/
theorem property_11 (pΛ m : ℕ) (p : ℤ) (hp : -2 ≤ p) (a b c : ℕ) (O I : Finset ℕ) (Y Z : List ℕ)
    (ha : a ∈ Finset.Icc 1 m) (hb : b ∈ Finset.Icc 1 m) (hc : c ∈ Finset.Icc 1 m)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hO : O ⊆ Finset.Icc 1 m)
    (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I) :
    (b ∈ O → c ∈ O →
      IsStack (clauseΓ1 pΛ b c p ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I) →
      LeadsTo (clauseΓ1 pΛ b c p ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I)
        {Y ++ interval (p + 1).toNat (p + 62).toNat ++ Z ++ literals pΛ m (O \ {b, c}) (I ∪ {b, c})}) ∧
    (a ∈ O → c ∈ O →
      IsStack (clauseΓ2 pΛ a c p ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I) →
      LeadsTo (clauseΓ2 pΛ a c p ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I)
        {Y ++ interval (p + 1).toNat (p + 62).toNat ++ Z ++ literals pΛ m (O \ {a, c}) (I ∪ {a, c})}) ∧
    (a ∈ O → b ∈ O →
      IsStack (clauseΓ3 pΛ a b p ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I) →
      LeadsTo (clauseΓ3 pΛ a b p ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I)
        {Y ++ interval (p + 1).toNat (p + 62).toNat ++ Z ++ literals pΛ m (O \ {a, b}) (I ∪ {a, b})}) := by sorry

end PancakeHard
