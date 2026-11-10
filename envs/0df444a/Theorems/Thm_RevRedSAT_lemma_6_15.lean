-- Prove2me | Theorems.Thm_RevRedSAT_lemma_6_15
-- name    : RevRedSAT.lemma_6_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:42.362888+00:00
-- url     : https://prove2.me/theorems/bb21e13c-f120-4a2b-a413-c77bec57c5e5
-- title:
--   Lemma 6.15 — a family $L_{n,r}$ of $O(r\log(n+1))$ maps making every r-set a forest
-- statement:
--   There are an algorithm and an absolute constant $K$ such that for all integers $1\le r\le n$, with $[n]$ the elements and $[8r]$ the buckets, the algorithm constructs a family $L_{n,r}$ of maps $h:[n]\to\binom{[8r]}{2}$ with
--
--   1. $|L_{n,r}|\le K\,r\log_2(n+1)$;
--   2. for every $S\subseteq[n]$ with $|S|\le r$ there is $h\in L_{n,r}$ whose bucket multigraph on $S$ (one edge $h(u)$ per $u\in S$) is a forest, and hence an injective $\phi:S\to[8r]$ with $\phi(u)\in h(u)$;
--   3. the construction, including the explicit list of all maps, takes at most $2^{K\,r\log_2(n+1)}$ steps.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the family is constructed explicitly → on input (n, r) the machine outputs the code of the list of maps (encMaps); reason: an explicit list of the maps
--   - encoding: O(r log(n + 1)), 2^{O(r log(n+1))} → K·r·log₂(n + 1) and ⌊2^{K r log₂(n+1)}⌋ for one absolute K; reason: the meaning of O
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.15, p.46 (printed) = PDF p.48

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_Placeable

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- **Lemma 6.15 (a family of maps for small selected sets).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.15, p.46: "Let 1 ≤ r ≤ n be integers. Regard [n] as the elements and [8r] as the
storage buckets. One can deterministically construct a family L_{n,r} of maps h : [n] → ([8r] choose 2),
where h(u) is the pair of distinct buckets allowed for element u, with the following guarantees:
1. The family has size O(r log(n + 1)). 2. For every S ⊆ [n] with |S| ≤ r, there is a map
h ∈ L_{n,r} for which the graph on the buckets, with one edge labeled u joining the pair h(u) for
every u ∈ S, is a forest. Thus there is an injective assignment ϕ : S → [8r] with ϕ(u) ∈ h(u) for
every u ∈ S; see Figure 5. 3. Constructing the family, including the explicit list of all its maps,
takes 2^{O(r log(n+1))} bit operations."

There are a finite-alphabet machine and an absolute constant `K` such that for all `1 ≤ r ≤ n`, on
input `(n, r)` the machine outputs within `⌊2^{K r log₂(n+1)}⌋` steps the list of a family of maps
`h : [n] → ([8r] choose 2)` of size at most `K r log₂(n + 1)` such that every `S` with `|S| ≤ r` has a
map in the family under which its bucket multigraph is a forest and its elements are placed in
distinct allowed buckets.

**Formalization Note** Maps are `Fin n → Finset (Fin (8r))` with 2-element values; the family is
listed with its maps in the code `encMaps`. -/
theorem lemma_6_15 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ K : ℝ,
      ∀ n r : ℕ, 1 ≤ r → r ≤ n →
        ∃ hs : List (Fin n → Finset (Fin (8 * r))),
          (∀ h ∈ hs, ∀ u, (h u).card = 2) ∧
          (hs.length : ℝ) ≤ K * r * Real.logb 2 (n + 1) ∧
          (∀ S : Finset (Fin n), S.card ≤ r → ∃ h ∈ hs, IsForestOn h S ∧ Placeable h S) ∧
          HMBinPacking.OutputsWithin M (encNat n ++ encNat r) (encMaps hs)
            ⌊(2 : ℝ) ^ (K * r * Real.logb 2 (n + 1))⌋₊ := by sorry

end RevRedSAT
