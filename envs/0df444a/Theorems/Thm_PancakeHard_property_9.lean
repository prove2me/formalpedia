-- Prove2me | Theorems.Thm_PancakeHard_property_9
-- name    : PancakeHard.property_9
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T07:03:42.945811+00:00
-- url     : https://prove2.me/theorems/342bc4b7-6fc8-49c0-9148-0118fe993274
-- title:
--   Property 9 — variable gadget (a. choice of $P$ or $N$, b.–c. completion)
-- statement:
--   Let $p_\Lambda$ and $m$ be fixed and $\Lambda^O_I$ be taken from $Literals(p_\Lambda,m)$. Let $P$, $N$ be disjoint subsets of $\llbracket 1;m\rrbracket$, $O$, $I$ disjoint subsets of $\llbracket 1;m\rrbracket$, $X$, $Y$ any sequences, and $(\nu,V,D)=Variable(P,N,p)$. Then
--
--   1. $\langle\nu,X,V,Y,\Lambda^O_I\rangle\Longrightarrow\{\langle X,V^1,Y,\Lambda^{O\cup P}_I\rangle,\ \langle X,V^2,Y,\Lambda^{O\cup N}_I\rangle\}$;
--   2. $\langle V^1,X,D,Y,\Lambda^O_I\rangle\Longrightarrow\langle X,\mathcal I^{p+1}_{p+31},Y,\Lambda^{O\cup N}_I\rangle$;
--   3. $\langle V^2,X,D,Y,\Lambda^O_I\rangle\Longrightarrow\langle X,\mathcal I^{p+1}_{p+31},Y,\Lambda^{O\cup P}_I\rangle$.
--
--   The paper requires $(P\cup N)\cap(O\cup I)=\emptyset$ for part 1, $N\cap(O\cup I)=\emptyset$ for part 2 and $P\cap(O\cup I)=\emptyset$ for part 3, and notes that these hold because all sequences considered are permutations. A variable gadget thus opens either the locks of the positive or of the negative occurrences of its variable.
--
--   **Formalization Note** The sets $P$, $N$ are given by enumerations (lists without repetition) that fix the order of the keys in $V$, $V^1$, $V^2$; the statement holds for every enumeration. The three side conditions are not separate hypotheses: the hypothesis that the left-hand sequence is a permutation implies each of them.
--
--
--   **Formalization Note** Sequences are lists of natural numbers with the head first; the statement assumes, as the paper does throughout (p.2, p.13), that the left-hand sequence is a permutation of $\llbracket 1 ; n\rrbracket$, where $n$ is its length. The context sequences may be empty.
--
--   Differences from the source:
--   - encoding: a sequence ⟨x₁, …, xₙ⟩ with head element x₁ → a list of natural numbers whose first entry is the head; reason: Lean convention; same instances
--   - reading: X, Y (, Z) are any sequences → the left-hand sequence is a permutation of ⟦1 ; n⟧, n its length (IsStack); X, Y, Z stay arbitrary and may be empty; reason: p.2: input sequences are permutations of ⟦1 ; n⟧; p.13: all sequences considered are permutations
--   - encoding: p is an integer → p : ℤ with -2 ≤ p, offsets written (p + c).toNat; p_Λ and m are natural numbers; reason: the least entry of V is p + 3 and a stack has entries ≥ 1, so p < −2 gives no stack; p = −2 and p = −1 do occur, in part a.; for p ≥ −2 each (p + c).toNat is p + c; a Literals gadget with m ≥ 1 contains p_Λ + 1; same instances
--   - encoding: a path is a series of flips, which goes through T → the list of visited sequences, consecutive ones related by an efficient flip; T is visited if it is in the list, endpoints included; reason: a flip sequence and its visited sequences determine each other on permutations; p.4 (Lemma 13) and Property 2 count endpoints
--   - encoding: O, I disjoint subsets of ⟦1 ; m⟧ → Finset ℕ with O, I ⊆ Icc 1 m and Disjoint O I; reason: same instances
--   - encoding: sets P = {p₁, …, p_q}, N = {n₁, …, n_q′} → duplicate-free lists [p₁, …, p_q], [n₁, …, n_q′] (their enumerations); reason: V, V¹, V² depend on the enumeration, which the paper leaves open; the statement quantifies over all
--   - encoding: side conditions (P ∪ N) ∩ (O ∪ I) = ∅ (a.), N ∩ (O ∪ I) = ∅ (b.), P ∩ (O ∪ I) = ∅ (c.) → not separate hypotheses; reason: the paper notes they are implied because all sequences are permutations: a violation repeats a key or test value; same instances
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.2.2, p.13, Property 9

import Mathlib
import Definitions.Def_PancakeHard_Variable

set_option autoImplicit false

namespace PancakeHard

/-- **Property 9** (variable gadget; Bulteau, Fertin, Rusu, *Pancake Flipping Is Hard*, arXiv:1111.0434v2, §3.2.2, p.13): "Let P, N be two disjoint subsets of
⟦1 ; m⟧, p be an integer, X and Y be two sequences, O, I be two disjoint subsets of ⟦1 ; m⟧, and
(ν, V, D) = Variable(P, N, p). For sub-property (a.) we require that (P ∪ N) ∩ (O ∪ I) = ∅, for (b.)
that N ∩ (O ∪ I) = ∅, and for (c.) that P ∩ (O ∪ I) = ∅ (these conditions are in fact necessarily
satisfied by construction since all sequences considered are permutations). We have
a. ⟨ν, X, V, Y, Λ^O_I⟩ ⟹ {⟨X, V¹, Y, Λ^{O∪P}_I⟩, ⟨X, V², Y, Λ^{O∪N}_I⟩}
b. ⟨V¹, X, D, Y, Λ^O_I⟩ ⟹ ⟨X, 𝓘^{p+1}_{p+31}, Y, Λ^{O∪N}_I⟩
c. ⟨V², X, D, Y, Λ^O_I⟩ ⟹ ⟨X, 𝓘^{p+1}_{p+31}, Y, Λ^{O∪P}_I⟩"
Here `Λ^O_I` is that of `Literals(p_Λ, m)` for fixed `p_Λ` and `m` (p.13).

**Formalization Note** "Any sequences" are read with the paper's convention (p.2; p.13: "all sequences considered are permutations"): the left-hand sequence is a stack, a permutation of `⟦1 ; n⟧` with `n` its length; `X`, `Y`, `Z` may be empty. The head is the first list entry. The sets `P = {p₁, …, p_q}`, `N = {n₁, …, n_{q′}}` are given by their enumerations (lists
without repetition), which fix the order of the keys in `V`, `V¹`, `V²`; the statement holds for every
enumeration. The side conditions `(P ∪ N) ∩ (O ∪ I) = ∅` etc. are not separate hypotheses: as the
paper says, the stack hypothesis implies them. `p` is an integer, as on the page: `p = −2` and
`p = −1` occur in part a. (the least entry of `V` is `p + 3`); `-2 ≤ p` excludes no instance, since
below it `V` has a nonpositive entry, and it makes each `(p + c).toNat` the page's `p + c`. In parts
b. and c. `D` contains `p + 1`, so the stack hypothesis gives `p ≥ 0`. -/
theorem property_9 (pΛ m : ℕ) (p : ℤ) (hp : -2 ≤ p) (P N : List ℕ) (O I : Finset ℕ) (X Y : List ℕ)
    (hP : P.Nodup) (hN : N.Nodup) (hPm : ∀ j ∈ P, j ∈ Finset.Icc 1 m)
    (hNm : ∀ j ∈ N, j ∈ Finset.Icc 1 m) (hPN : P.Disjoint N) (hO : O ⊆ Finset.Icc 1 m)
    (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I) :
    (IsStack (varNu p :: X ++ varV pΛ P N p ++ Y ++ literals pΛ m O I) →
      LeadsTo (varNu p :: X ++ varV pΛ P N p ++ Y ++ literals pΛ m O I)
        {X ++ varV1 pΛ N p ++ Y ++ literals pΛ m (O ∪ P.toFinset) I,
          X ++ varV2 pΛ P p ++ Y ++ literals pΛ m (O ∪ N.toFinset) I}) ∧
    (IsStack (varV1 pΛ N p ++ X ++ varD p ++ Y ++ literals pΛ m O I) →
      LeadsTo (varV1 pΛ N p ++ X ++ varD p ++ Y ++ literals pΛ m O I)
        {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++ literals pΛ m (O ∪ N.toFinset) I}) ∧
    (IsStack (varV2 pΛ P p ++ X ++ varD p ++ Y ++ literals pΛ m O I) →
      LeadsTo (varV2 pΛ P p ++ X ++ varD p ++ Y ++ literals pΛ m O I)
        {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++ literals pΛ m (O ∪ P.toFinset) I}) := by sorry

end PancakeHard
