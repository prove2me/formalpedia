-- Prove2me | Theorems.Thm_RevRedSAT_lemma_6_14
-- name    : RevRedSAT.lemma_6_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:15.759195+00:00
-- url     : https://prove2.me/theorems/78b3634c-4313-43a0-8590-2343781a1d75
-- title:
--   Lemma 6.14 — the encoding for arbitrary maps, with $O(qD)$ variables
-- statement:
--   There is an absolute constant $K$ such that for every fixed $d\ge2$ the following holds. Let $\mathcal H$ be a rank-$d$ family with $m$ sets and support $[n]$, where $n>k\ge1$. Let $c\in\{1,2\}$ and $q\ge\max\{k,c\}$, and give each element $u$ a set $g(u)\subseteq[q]$ of exactly $c$ allowed buckets. Put $D=1+\log_2(1+n/q)$. In time polynomial in $n+m+q$ one can construct a CNF formula $F_g$ with
--
--   $$N\le KqD\ \text{variables},\qquad M=O_d(mD^{cd}+q)\ \text{clauses},\qquad\text{width}\le\max\{3,cd\},$$
--
--   and a decoder, such that every satisfying assignment gives a hitting set of size at most $k$, and $F_g$ is satisfiable whenever some hitting set of size at most $k$ can be placed in distinct allowed buckets. No bound on the bucket loads is assumed.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: every satisfying assignment gives a hitting set → the machine outputs a decoder, a list of (element, conjunction of literals); reason: the read-out must be fixed before the assignment
--   - encoding: time polynomial in n + m + q for fixed d → C·(n + m + q + 1)^e with C, e after d; reason: the meaning of the phrase
--   - encoding: M clauses → the number of clauses counted with multiplicity; reason: at least the number of distinct clauses
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.14, p.46 (printed) = PDF p.48

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

/-- **Lemma 6.14 (the encoding for arbitrary maps, by list splitting).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.14, p.46: "Let H be a rank-d family with m sets and support [n], where n > k ≥ 1. Let
c ∈ {1, 2} and q ≥ max{k, c}, and give each element u a set g(u) ⊆ [q] of exactly c allowed
buckets. Put D = 1 + log2(1 + n/q). In time polynomial in n + m + q for fixed d, one can construct
a CNF formula F_g with N = O(qD) variables, M = O_d(mD^{cd} + q) clauses, and width at most
max{3, cd}. Every satisfying assignment gives a hitting set of size at most k. Conversely, if some
hitting set of size at most k can be assigned to distinct allowed buckets, then F_g is satisfiable."

There is an absolute constant `K` such that for every `d ≥ 2` there are a finite-alphabet machine and
constants `K_d, C, e` with: for every such `H`, `k`, `c`, `q`, `g`, on input `n`, a listing of `H`,
`k`, `q` and `g`, the machine outputs within `C·(n + m + q + 1)^e` steps a formula `F_g` and a
decoder with at most `K·q·D` variables, at most `K_d·(m D^{cd} + q)` clauses, width at most
`max{3, cd}`, the decoder reading a hitting set of size at most `k` from every satisfying
assignment, and `F_g` satisfiable whenever a hitting set of size at most `k` can be placed in
distinct allowed buckets.

**Formalization Note** Decoder and clause count as in `lemma_6_8`; no bound on the bucket loads is
assumed. -/
theorem lemma_6_14 :
    ∃ K : ℕ, ∀ d : ℕ, 2 ≤ d →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ (Kd : ℝ) (C e : ℕ),
        ∀ (n m k c q : ℕ) (H : Finset (Finset (Fin n))) (g : Fin n → Finset (Fin q)),
          (∀ S ∈ H, S.card ≤ d) → H.card = m → supp H = Finset.univ → 1 ≤ k → k < n →
          (c = 1 ∨ c = 2) → max k c ≤ q → (∀ u, (g u).card = c) →
          ∀ LH : List (List (Fin n)), IsListing H LH →
            ∃ (N : ℕ) (φ : MainResults.CNF N) (dec : List (Fin n × List (Fin N × Bool))),
              HMBinPacking.OutputsWithin M
                (encNat n ++ encFamily LH ++ encNat k ++ encNat q ++ encMap g)
                (encCNF φ ++ encDecoder dec) (C * (n + m + q + 1) ^ e) ∧
              (N : ℝ) ≤ K * q * (1 + Real.logb 2 (1 + (n : ℝ) / q)) ∧
              (φ.length : ℝ) ≤ Kd * (m * (1 + Real.logb 2 (1 + (n : ℝ) / q)) ^ (c * d) + q) ∧
              width φ ≤ max 3 (c * d) ∧
              (∀ a : Fin N → Bool, SatBy a φ →
                AlgebraicFPT.HittingSet.IsHitting H (readout dec a) ∧ (readout dec a).card ≤ k) ∧
              ((∃ X : Finset (Fin n), AlgebraicFPT.HittingSet.IsHitting H X ∧ X.card ≤ k ∧
                Placeable g X) → MainResults.Satisfiable φ) := by sorry

end RevRedSAT
