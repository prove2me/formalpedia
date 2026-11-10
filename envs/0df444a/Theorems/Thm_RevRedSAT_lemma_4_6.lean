-- Prove2me | Theorems.Thm_RevRedSAT_lemma_4_6
-- name    : RevRedSAT.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:44.89719+00:00
-- url     : https://prove2.me/theorems/e64b67b2-6259-4238-9ec2-5790253d81a6
-- title:
--   Lemma 4.6 — a cardinality constraint in 3-CNF with unique extensions
-- statement:
--   There are a polynomial-time algorithm and an absolute constant $K$ such that for all integers $a\ge1$ and $0\le k\le a$ the algorithm constructs a CNF formula $\varphi$ of width at most $3$ over $n$ variables, $a\le n\le Ka$, the first $a$ of which are $x_1,\dots,x_a$, with at most $Ka$ clauses, that enforces
--
--   $$x_1+\cdots+x_a\le k.$$
--
--   More precisely, every assignment of $x_1,\dots,x_a$ with at most $k$ ones has exactly one extension to the auxiliary variables satisfying $\varphi$, and every assignment with more than $k$ ones has none. The unique extension property is what allows the same constraint in counting reductions.
--
--   **Formalization Note** The input of the algorithm is $(a,k)$ and its running time is polynomial in $a$; the variables $x_i$ are the formula variables $0,\dots,a-1$.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - reading: in polynomial time (the variables x_1, …, x_a are given) → time ≤ C·(a + 1)^e on input (a, k); reason: the output has Θ(a) clauses, so polynomial means polynomial in a, not in the binary length of a
--   - encoding: the formula is on x_1, …, x_a and auxiliary variables → x_i is the formula variable i − 1; the auxiliary variables are the remaining ones; reason: a naming convention
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 4.6, p.31 (printed) = PDF p.33

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_encCNF

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- **Lemma 4.6 (a cardinality constraint with unique extensions).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 4.6, p.31: "Let x1, . . . , xa be Boolean variables, where a ≥ 1, and let k be an integer
with 0 ≤ k ≤ a. In polynomial time, one can construct a 3-CNF formula on these variables and
auxiliary variables, with O(a) variables and clauses in total, that enforces x1 + · · · + xa ≤ k.
More precisely, each assignment to x1, . . . , xa with at most k ones has exactly one satisfying
extension to the auxiliary variables. An assignment with more than k ones has none."

There are a finite-alphabet machine and absolute constants `K, C, e` such that for all `1 ≤ a` and
`0 ≤ k ≤ a`, on input `(a, k)` the machine outputs within `C·(a + 1)^e` steps the code of a formula
`φ` of width at most `3` over `n` variables, `a ≤ n ≤ K·a`, with at most `K·a` clauses, whose first
`a` variables are `x₁, …, x_a`: every assignment `x` with at most `k` ones has exactly one extension
satisfying `φ`, and every assignment with more than `k` ones has none.

**Formalization Note** "Polynomial time" is polynomial in `a` (the variables are listed), not in the
binary length of `(a, k)`, which would not even allow writing the formula. The variables `x_i` are
the formula variables `0, …, a − 1`. -/
theorem lemma_4_6 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ K C e : ℕ,
      ∀ a k : ℕ, 1 ≤ a → k ≤ a →
        ∃ (n : ℕ) (φ : MainResults.CNF n) (h : a ≤ n),
          HMBinPacking.OutputsWithin M (encNat a ++ encNat k) (encCNF φ) (C * (a + 1) ^ e) ∧
          width φ ≤ 3 ∧ n ≤ K * a ∧ φ.length ≤ K * a ∧
          ∀ x : Fin a → Bool,
            ((Finset.univ.filter fun i => x i = true).card ≤ k →
              ∃! y : Fin n → Bool, (∀ i, y (Fin.castLE h i) = x i) ∧ SatBy y φ) ∧
            (k < (Finset.univ.filter fun i => x i = true).card →
              ∀ y : Fin n → Bool, (∀ i, y (Fin.castLE h i) = x i) → ¬ SatBy y φ) := by sorry

end RevRedSAT
