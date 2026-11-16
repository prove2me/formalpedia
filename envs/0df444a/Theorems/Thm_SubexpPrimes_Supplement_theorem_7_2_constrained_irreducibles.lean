-- Prove2me | Theorems.Thm_SubexpPrimes_Supplement_theorem_7_2_constrained_irreducibles
-- name    : SubexpPrimes.Supplement.theorem_7_2_constrained_irreducibles
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:47:54.581856+00:00
-- url     : https://prove2.me/theorems/ac07f59b-35c5-4e93-b44b-24c1c87bb7fa
-- title:
--   Theorem 7.2 — exact count, least element, rank and unrank of constrained irreducibles over $\mathbb F_2$
-- statement:
--   Let $C$ be an **admissible** constraint (Definition 2.3) on the $n$ free coefficients of monic degree-$n$ polynomials over $\mathbb F_2$, given by a description $d$ of length $L$. Let $I_n(C)$ be the number of irreducible monic polynomials of degree $n$ over $\mathbb F_2$ accepted by $C$. Then each of the following can be done by a single deterministic machine in time
--
--   $$
--   \mathrm{poly}(n+L)\,2^{O(n/\sqrt{\log n})}
--   $$
--
--   and polynomial space:
--
--   1. compute $I_n(C)$ exactly;
--   2. find the least accepted irreducible in coefficient order, or report that there is none;
--   3. given an accepted irreducible $F$, output its rank, the number of accepted irreducibles below it in coefficient order;
--   4. given $k<I_n(C)$, output the accepted irreducible of rank $k$.
--
--   The theorem gives exact counts of irreducible polynomials with prescribed coefficients, where previously only exhaustive search over $2^n$ candidates was known deterministically.
--
--   **Formalization Note** Admissibility is a property of the family $(n,d)\mapsto C$ and the machines and constants may depend on that family, never on $n$ or $d$. Time is $K(n+L+1)^K2^{Kn/\sqrt{\log_2 n}}$ and space $K(n+L+1)^K$. The rank input is the free-coefficient string of $F$, and the unrank input the $n$-bit string of $k$.
--
--   Differences from the source:
--   - encoding: the n free coefficients of a monic degree-n polynomial; coefficient order → the n-bit string f_{n−1}…f_0, most significant first, with F = polyOf (true :: x); order of the strings as n-bit integers (bitsToNat); reason: the paper's convention for words as polynomials (p.13) and the prefix search from the top coefficient (p.33)
--   - encoding: poly(n + L) 2^{O(n/√log n)} and polynomial space → K (n+L+1)^K 2^{K n/√(log₂ n)} steps and K (n+L+1)^K cells; reason: one constant K for both polynomial factors; same instances
--   - reading: with the same bound, one can find the least …, and rank and unrank → four conjuncts, each with its own machine and constant; reason: four different input–output tasks; each has the stated bound
--   - reading: the rank of an accepted irreducible F is the number of accepted irreducibles below it → irrRank, the number of accepted strings strictly below x, so ranks start at 0; unrank is its inverse on k < Iₙ(C); reason: the source's definition, p.33
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem 7.2, p.31 (PDF p.33); proof pp.32–33; Definition 2.3, p.15

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_RunsWithin
import Definitions.Def_SubexpPrimes_bitsToNat
import Definitions.Def_SubexpPrimes_Admissible
import Definitions.Def_SubexpPrimes_prefixSearch
import Definitions.Def_SubexpPrimes_Supplement_irrCount

set_option autoImplicit false

namespace SubexpPrimes.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 7.2 (Constrained irreducibles)** — Gajulapalli, *Deterministic Construction of Primes
in Subexponential Time* (manuscript, sha256 6ad4d3de…), p.31.

Let `C` be an admissible constraint on the `n` free coefficients of monic degree-`n` polynomials over
`F₂`, with description `d` of length `L`. Then, each in time `poly(n + L) 2^{O(n/√log n)}` and
polynomial space:
1. the number `Iₙ(C)` of accepted irreducibles is computed exactly;
2. the least accepted irreducible in coefficient order is found, or "none" is reported;
3. an accepted irreducible is ranked (the number of accepted irreducibles below it);
4. a rank `k < Iₙ(C)` is unranked (the accepted irreducible of rank `k` is output).

**Formalization Note.** Admissibility is the published `Admissible` (Definition 2.3), a property of
the family `(n, d) ↦ C n d`; each machine and constant `K` may depend on the family and its constants,
never on `n` or `d`. Inputs start with `admissibleInput n (encD d)` (that is `(1ⁿ, d)`); the rank input
adds the free-coefficient string `x`, the unrank input the `n`-bit string of `k`. Time is
`subexpBound K (n + L) n = K (n+L+1)^K 2^{K n/√(log₂ n)}`, space `polyBound K (n + L)`. Coefficient
order is the order of free-coefficient strings as `n`-bit integers (`bitsToNat`), most significant
coefficient first. -/
theorem theorem_7_2_constrained_irreducibles :
    ∀ {δ : Type} (encD : δ → List Bool) (C : ℕ → δ → List Bool → Prop), Admissible encD C →
      -- the exact count
      (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
        ∀ (n : ℕ) (d : δ),
          RunsWithin M out (admissibleInput n (encD d)) (countWord (irrCount n (C n d)))
            (subexpBound K (n + (encD d).length) n) (polyBound K (n + (encD d).length))) ∧
      -- the least accepted irreducible, or none
      (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
        ∀ (n : ℕ) (d : δ), ∃ o : Option (List Bool),
          IsSearchAnswer n (IrrAccepted (C n d)) o ∧
          RunsWithin M out (admissibleInput n (encD d)) (searchWord o)
            (subexpBound K (n + (encD d).length) n) (polyBound K (n + (encD d).length))) ∧
      -- rank
      (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
        ∀ (n : ℕ) (d : δ) (x : List Bool), x.length = n → IrrAccepted (C n d) x →
          RunsWithin M out (Encoding.encodeList id [admissibleInput n (encD d), x])
            (countWord (irrRank n (C n d) x))
            (subexpBound K (n + (encD d).length) n) (polyBound K (n + (encD d).length))) ∧
      -- unrank
      (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
        ∀ (n : ℕ) (d : δ) (k : ℕ), k < irrCount n (C n d) →
          ∃ x : List Bool, x.length = n ∧ IrrAccepted (C n d) x ∧ irrRank n (C n d) x = k ∧
            RunsWithin M out (Encoding.encodeList id [admissibleInput n (encD d), bitsOf n k]) x
              (subexpBound K (n + (encD d).length) n)
              (polyBound K (n + (encD d).length))) := by sorry

end SubexpPrimes.Supplement
