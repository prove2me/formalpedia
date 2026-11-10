-- Prove2me | Theorems.Thm_RevRedSAT_lemma_6_16
-- name    : RevRedSAT.lemma_6_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:54.304205+00:00
-- url     : https://prove2.me/theorems/8615256a-2a23-454c-a466-cce6c31422c3
-- title:
--   Lemma 6.16 — combining the local maps over intervals: $8k\le Q\le16k$, $|\mathcal G|\le(n+1)^{b-1}|L_{n,r}|^b$
-- statement:
--   Let $M_{15}$ be an algorithm with the guarantees of Lemma 6.15, whose output on $(n,r)$ is the family $L_{n,r}$. Let $n>k\ge1$ and put $L_0=\lceil\log_2(k+2)\rceil$, $r=\min\{k,L_0^2\}$, $b=\lceil k/r\rceil$ and $Q=8rb$. Then $8k\le Q\le16k$, and one can construct a family $\mathcal G$ of maps $g:[n]\to\binom{[Q]}{2}$ such that
--
--   1. every $S\subseteq[n]$ with $|S|\le k$ has an injective $\phi:S\to[Q]$ with $\phi(u)\in g(u)$ for some $g\in\mathcal G$;
--   2. $|\mathcal G|\le(n+1)^{b-1}|L_{n,r}|^b$;
--   3. for each fixed $a\ge0$ and $C\ge1$, if $n\le CkL_0^a$, the complete construction and explicit enumeration take $2^{O_{a,C}(L_0^3+k/L_0)}$ steps.
--
--   **Formalization Note** The construction is one machine on input $(n,k)$; the constant in item 3 depends on $(a,C)$ only.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - reading: L_{n,r}, the family from Lemma 6.15 → the output on (n, r) of a machine M₁₅ assumed to satisfy the three guarantees of Lemma 6.15; reason: the source refers to the construction of Lemma 6.15; any construction with its guarantees serves, and Lemma 6.15's own construction is an instance
--   - encoding: 2^{O_{a,C}(L₀³ + k/L₀)} → 2^{K(a,C)·(L₀³ + k/L₀)} for a function K of (a, C) chosen with the machine; reason: the meaning of O_{a,C}
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.16, p.47 (printed) = PDF p.49

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_Placeable

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- **Lemma 6.16 (combining the local maps over intervals).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.16, p.47: "Let n > k ≥ 1, and put L0 = ⌈log2(k + 2)⌉, r = min{k, L0²}, b = ⌈k/r⌉, and
Q = 8rb. Let L_{n,r} be the family from Lemma 6.15, whose maps assign each element of [n] two allowed
buckets among 8r buckets. One can construct a family G of maps g : [n] → ([Q] choose 2) such that
every S ⊆ [n], |S| ≤ k, has an injective assignment ϕ : S → [Q] satisfying ϕ(u) ∈ g(u) for some
g ∈ G. Moreover, 8k ≤ Q ≤ 16k and |G| ≤ (n + 1)^{b−1}|L_{n,r}|^b. For each fixed a ≥ 0 and C ≥ 1, if
n ≤ CkL0^a, the complete deterministic construction and explicit enumeration take
2^{O_{a,C}(L0³+k/L0)} bit operations."

Let `M₁₅` be a machine with constant `K₁₅` satisfying the guarantees of Lemma 6.15 (its output on
`(n, r)` is the family `L_{n,r}`). Then there are a finite-alphabet machine `M` and constants
`K(a, C)` such that for all `n > k ≥ 1`, with `L₀, r, b, Q` as above (`cutL0`, `cutR`, `cutB`,
`cutQ`): `8k ≤ Q ≤ 16k`; and on input `(n, k)` the machine outputs, within some number `t` of steps,
the list of a family `G` of maps `g : [n] → ([Q] choose 2)` such that every `S` with `|S| ≤ k` is
placed in distinct allowed buckets by some `g ∈ G`, `|G| ≤ (n + 1)^{b−1}|L_{n,r}|^b`, and
`t ≤ 2^{K(a,C)(L₀³ + k/L₀)}` whenever `a ≥ 0`, `C ≥ 1` and `n ≤ C k L₀^a`.

**Formalization Note** "The family from Lemma 6.15" is the output of any machine with Lemma 6.15's
guarantees, taken as a hypothesis (`h₁₅` restates guarantees 1–3 of `lemma_6_15` for `M₁₅`). -/
theorem lemma_6_16 (M₁₅ : Turing.TM2ComputableAux Bool Bool) (K₁₅ : ℝ)
    (h₁₅ : ∀ n r : ℕ, 1 ≤ r → r ≤ n →
      ∃ hs : List (Fin n → Finset (Fin (8 * r))),
        (∀ h ∈ hs, ∀ u, (h u).card = 2) ∧
        (hs.length : ℝ) ≤ K₁₅ * r * Real.logb 2 (n + 1) ∧
        (∀ S : Finset (Fin n), S.card ≤ r → ∃ h ∈ hs, IsForestOn h S ∧ Placeable h S) ∧
        HMBinPacking.OutputsWithin M₁₅ (encNat n ++ encNat r) (encMaps hs)
          ⌊(2 : ℝ) ^ (K₁₅ * r * Real.logb 2 (n + 1))⌋₊) :
    ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ K : ℕ → ℝ → ℝ,
      ∀ n k : ℕ, 1 ≤ k → k < n →
        8 * k ≤ cutQ k ∧ cutQ k ≤ 16 * k ∧
        ∃ (G : List (Fin n → Finset (Fin (cutQ k)))) (t : ℕ),
          (∀ g ∈ G, ∀ u, (g u).card = 2) ∧
          (∀ S : Finset (Fin n), S.card ≤ k → ∃ g ∈ G, Placeable g S) ∧
          (∀ (hs : List (Fin n → Finset (Fin (8 * cutR k)))) (t' : ℕ),
            HMBinPacking.OutputsWithin M₁₅ (encNat n ++ encNat (cutR k)) (encMaps hs) t' →
            G.length ≤ (n + 1) ^ (cutB k - 1) * hs.length ^ cutB k) ∧
          HMBinPacking.OutputsWithin M (encNat n ++ encNat k) (encMaps G) t ∧
          ∀ (a : ℕ) (C : ℝ), 1 ≤ C → (n : ℝ) ≤ C * k * (cutL0 k : ℝ) ^ a →
            (t : ℝ) ≤ (2 : ℝ) ^ (K a C * ((cutL0 k : ℝ) ^ 3 + (k : ℝ) / cutL0 k)) := by sorry

end RevRedSAT
