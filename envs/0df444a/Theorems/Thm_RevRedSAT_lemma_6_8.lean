-- Prove2me | Theorems.Thm_RevRedSAT_lemma_6_8
-- name    : RevRedSAT.lemma_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:57.378109+00:00
-- url     : https://prove2.me/theorems/ffb84e37-28d5-4d78-9fc1-24caa5cb65b2
-- title:
--   Lemma 6.8 — the activation/address encoding with $O(qA)$ variables
-- statement:
--   There is an absolute constant $K$ such that for every fixed $d\ge2$ the following holds. Let $\mathcal H$ be a rank-$d$ family with $m$ sets and support $[n]$, where $n>k\ge1$. Let $c\in\{1,2\}$ and $q\ge c$, and give each $u\in[n]$ exactly $c$ allowed buckets $g(u)\subseteq[q]$. Suppose every bucket has at most $B\ge1$ candidates, and put $A=1+\log_2B$. One can construct, in time polynomial in $n+m+q+\log B$, a CNF formula with
--
--   $$N\le KqA\ \text{variables},\qquad M=O_d(mA^{cd}+q)\ \text{clauses},\qquad \text{width}\le\max\{3,cd\},$$
--
--   together with a decoder, such that every satisfying assignment gives (through the decoder) a hitting set of $\mathcal H$ of size at most $k$; conversely, if some hitting set of size at most $k$ can be placed in distinct allowed buckets, the formula is satisfiable.
--
--   **Formalization Note** "Gives a hitting set" is made explicit by a decoder (pairs of an element and a conjunction of literals) output with the formula.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: every satisfying assignment gives a hitting set (recovery reads the active buckets and their addresses) → the machine outputs a decoder, a list of (element, conjunction of literals); the elements whose conjunction holds form the hitting set; reason: the read-out must be fixed before the assignment; the decoder is the proof's P_{u,j}
--   - encoding: time polynomial in n + m + q + log B for fixed d → C·(n + m + q + ⌊log₂ B⌋ + 1)^e with C, e after d; reason: the meaning of the phrase
--   - encoding: M clauses → the number of clauses counted with multiplicity; reason: at least the number of distinct clauses, so the bound is not weaker
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.8, p.42 (printed) = PDF p.44

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_AlgebraicFPT_HittingSet_HittingSets
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_encCNF
import Definitions.Def_RevRedSAT_IsHSCode
import Definitions.Def_RevRedSAT_frequency
import Definitions.Def_RevRedSAT_Placeable

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- **Lemma 6.8 (activation/address encoding of bucket contents).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.8, p.42: "Let H be a rank-d family with m sets and support [n], where n > k ≥ 1. Let
c ∈ {1, 2} and q ≥ c, and give each u ∈ [n] exactly c allowed buckets g(u) ⊆ [q]. Suppose every
bucket has at most B ≥ 1 candidates, and put A = 1 + log2 B. One can construct a CNF formula with
N = O(qA) variables, M = O_d(mA^{cd} + q) clauses, and width at most max{3, cd} in time polynomial
in n + m + q + log B for fixed d. Every satisfying assignment gives a hitting set of size at most k.
Conversely, if some hitting set of size at most k can be assigned to distinct allowed buckets, then
the formula is satisfiable."

There is an absolute constant `K` such that for every `d ≥ 2` there are a finite-alphabet machine and
constants `K_d, C, e` with: for every such `H`, `k`, `c`, `q`, `g`, `B`, on input `n`, a listing of
`H`, `k`, `q`, the map `g` and `B`, the machine outputs within
`C·(n + m + q + ⌊log₂ B⌋ + 1)^e` steps a formula `φ` and a decoder (pairs of an element and a
conjunction of literals) such that `φ` has at most `K·q·(1 + log₂ B)` variables, at most
`K_d·(m(1 + log₂ B)^{cd} + q)` clauses and width at most `max{3, cd}`; the decoder reads from every
satisfying assignment a hitting set of `H` of size at most `k`; and `φ` is satisfiable whenever some
hitting set of size at most `k` can be placed in distinct allowed buckets.

**Formalization Note** "Gives a hitting set" is made explicit by a decoder output with the formula
("Recovery reads the active buckets and their addresses", proof, p.42); the decoder is part of the
polynomial-time output. Clauses are counted with multiplicity. -/
theorem lemma_6_8 :
    ∃ K : ℕ, ∀ d : ℕ, 2 ≤ d →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ (Kd : ℝ) (C e : ℕ),
        ∀ (n m k c q B : ℕ) (H : Finset (Finset (Fin n))) (g : Fin n → Finset (Fin q)),
          (∀ S ∈ H, S.card ≤ d) → H.card = m → supp H = Finset.univ → 1 ≤ k → k < n →
          (c = 1 ∨ c = 2) → c ≤ q → (∀ u, (g u).card = c) → 1 ≤ B →
          (∀ b, bucketLoad g b ≤ B) →
          ∀ LH : List (List (Fin n)), IsListing H LH →
            ∃ (N : ℕ) (φ : MainResults.CNF N) (dec : List (Fin n × List (Fin N × Bool))),
              HMBinPacking.OutputsWithin M
                (encNat n ++ encFamily LH ++ encNat k ++ encNat q ++ encMap g ++ encNat B)
                (encCNF φ ++ encDecoder dec) (C * (n + m + q + Nat.log 2 B + 1) ^ e) ∧
              (N : ℝ) ≤ K * q * (1 + Real.logb 2 B) ∧
              (φ.length : ℝ) ≤ Kd * (m * (1 + Real.logb 2 B) ^ (c * d) + q) ∧
              width φ ≤ max 3 (c * d) ∧
              (∀ a : Fin N → Bool, SatBy a φ →
                AlgebraicFPT.HittingSet.IsHitting H (readout dec a) ∧ (readout dec a).card ≤ k) ∧
              ((∃ X : Finset (Fin n), AlgebraicFPT.HittingSet.IsHitting H X ∧ X.card ≤ k ∧
                Placeable g X) → MainResults.Satisfiable φ) := by sorry

end RevRedSAT
