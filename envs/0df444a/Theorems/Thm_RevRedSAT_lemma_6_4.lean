-- Prove2me | Theorems.Thm_RevRedSAT_lemma_6_4
-- name    : RevRedSAT.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:49.894487+00:00
-- url     : https://prove2.me/theorems/210b43d4-8df0-4d8a-81d2-ec022576e628
-- title:
--   Lemma 6.4 — a direct 3-CNF encoding of a sparse branch with $O_d(kT)$ variables
-- statement:
--   Fix $d\ge2$. Let $\mathcal H$ have rank at most $d$ and frequency at most $T$, let $k\ge0$ and let $B$ be a set of forbidden elements.
--
--   1. If $|\mathcal H|>kT$, no hitting set of size at most $k$ exists.
--   2. Otherwise, with $A=\operatorname{supp}(\mathcal H)$ and $a=|A|$, we have $a\le d|\mathcal H|\le dkT$, and one can construct in time polynomial in the input length (degree depending on $d$) a CNF formula of width at most $3$ such that
--      1. it is satisfiable if and only if some $Y\subseteq A$ hits $\mathcal H$, avoids $B$ and has $|Y|\le k$;
--      2. it has $O_d(a+|\mathcal H|)=O_d(kT)$ variables, clauses and literal occurrences;
--      3. it has one selection bit per element of $A$, and reading these bits from any satisfying assignment gives a set $Y$ with the properties of item 1.
--
--   **Formalization Note** The selection bits are output as a list of (element, variable) pairs.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: in polynomial time → a finite-alphabet machine and constants C, e chosen before the input, time ≤ C·(input size + 1)^e; reason: the standard meaning, with the constants fixed before the input
--   - encoding: one selection bit per element of A → the machine also outputs the list of pairs (u, x_u), u ∈ A, with distinct variables; reason: the correspondence must be given to read a set from an assignment
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.4, p.40 (printed) = PDF p.42

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_AlgebraicFPT_HittingSet_HittingSets
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_encCNF
import Definitions.Def_RevRedSAT_IsHSCode
import Definitions.Def_RevRedSAT_frequency

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- **Lemma 6.4 (direct encoding of a sparse branch).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.4, p.40: "Let H ⊆ 2^U have rank at most d and frequency at most T. Let k ≥ 0 be the
budget, and let B ⊆ U be the forbidden elements. If |H| > kT, no hitting set of size at most k
exists. Otherwise, put A = supp(H) and a = |A|; then a ≤ d|H| ≤ dkT. One can construct a 3-CNF
formula with the following properties: 1. The formula is satisfiable if and only if some set Y ⊆ A
hits H, avoids B, and satisfies |Y| ≤ k. 2. The formula has O_d(a + |H|) = O_d(kT) variables,
clauses, and literal occurrences. 3. There is one selection bit per element of A. Reading these bits
from any satisfying assignment recovers a set Y with the stated properties. Construction takes time
polynomial in the explicit input length, with degree depending only on d."

For every `d ≥ 2` there are a finite-alphabet machine and constants `K, C, e` such that for every
family `H` of rank at most `d` and frequency at most `T`, budget `k` and forbidden set `B`:
`|H| > kT` implies that no hitting set of size at most `k` exists; and if `|H| ≤ kT`, then
`a ≤ d|H| ≤ dkT`, and on input `n`, a listing of `H`, a listing of `B` and `k` the machine outputs
within `C·(|input| + 1)^e` steps a formula `φ` of width at most `3` and a list of selection pairs
`(u, x_u)` with: `φ` satisfiable iff some `Y ⊆ A` hits `H`, avoids `B`, `|Y| ≤ k`; at most
`K(a + |H|)` and at most `K·kT` variables, clauses and literal occurrences; the selected elements
are exactly `A`, with distinct selection variables; and for every satisfying assignment the
elements whose selection bit is `1` form such a set `Y`.

**Formalization Note** The selection bits are output by the machine as a list of pairs (element,
variable); the read-out of an assignment is the set of elements whose variable is true. -/
theorem lemma_6_4 :
    ∀ d : ℕ, 2 ≤ d →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ K C e : ℕ,
        ∀ (n : ℕ) (H : Finset (Finset (Fin n))) (T k : ℕ) (B : Finset (Fin n)),
          (∀ S ∈ H, S.card ≤ d) → frequency H ≤ T →
          (k * T < H.card →
            ¬ ∃ Y : Finset (Fin n), AlgebraicFPT.HittingSet.IsHitting H Y ∧ Y.card ≤ k) ∧
          (H.card ≤ k * T →
            (supp H).card ≤ d * H.card ∧ d * H.card ≤ d * k * T ∧
            ∀ (LH : List (List (Fin n))) (LB : List (Fin n)), IsListing H LH → LB.Nodup →
              LB.toFinset = B →
              ∃ (N : ℕ) (φ : MainResults.CNF N) (sel : List (Fin n × Fin N)),
                HMBinPacking.OutputsWithin M (encNat n ++ encFamily LH ++ encSet LB ++ encNat k)
                  (encCNF φ ++ encList (fun p => encFin p.1 ++ encFin p.2) sel)
                  (C * ((encNat n ++ encFamily LH ++ encSet LB ++ encNat k).length + 1) ^ e) ∧
                width φ ≤ 3 ∧
                (MainResults.Satisfiable φ ↔ ∃ Y ⊆ supp H,
                  AlgebraicFPT.HittingSet.IsHitting H Y ∧ Disjoint Y B ∧ Y.card ≤ k) ∧
                N ≤ K * ((supp H).card + H.card) ∧ φ.length ≤ K * ((supp H).card + H.card) ∧
                litOcc φ ≤ K * ((supp H).card + H.card) ∧
                N ≤ K * (k * T) ∧ φ.length ≤ K * (k * T) ∧ litOcc φ ≤ K * (k * T) ∧
                (sel.map Prod.fst).toFinset = supp H ∧ (sel.map Prod.fst).Nodup ∧
                (sel.map Prod.snd).Nodup ∧
                ∀ a : Fin N → Bool, SatBy a φ →
                  ((sel.filter fun p => a p.2).map Prod.fst).toFinset ⊆ supp H ∧
                  AlgebraicFPT.HittingSet.IsHitting H ((sel.filter fun p => a p.2).map Prod.fst).toFinset ∧
                  Disjoint ((sel.filter fun p => a p.2).map Prod.fst).toFinset B ∧
                  ((sel.filter fun p => a p.2).map Prod.fst).toFinset.card ≤ k) := by sorry

end RevRedSAT
