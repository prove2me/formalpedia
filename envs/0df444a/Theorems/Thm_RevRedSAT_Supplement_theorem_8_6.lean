-- Prove2me | Theorems.Thm_RevRedSAT_Supplement_theorem_8_6
-- name    : RevRedSAT.Supplement.theorem_8_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:03:51.713714+00:00
-- url     : https://prove2.me/theorems/56985739-f211-47f9-a4cc-408fb1a19154
-- title:
--   Theorem 8.6 — a connected dominating set of size $b<n$ in $2^{O(n\eta(n)^3/\sqrt{\lambda(n)})}$, success 2/3
-- statement:
--   Assume the Counting $d$-SAT Assumption 4.5. There are a randomized algorithm and a constant $C$ that, given an $n$-vertex graph $G$ and a budget $b<n$, either find a connected dominating set of size at most $b$ or report NO, within
--
--   $$\Bigl\lfloor 2^{C\,n\eta(n)^3/\sqrt{\lambda(n)}}\Bigr\rfloor$$
--
--   steps on every random string. On a YES instance a set is returned with probability at least $2/3$; on a NO instance the algorithm always reports NO.
--
--   Combined with a linear-vertex kernel, this gives Theorem 8.7 for Max Leaf Spanning Tree.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: a randomized algorithm with no false positives and the stated success probability → MonteCarloWithin (EdgeMonteCarloWithin for edge-set solutions): ρ(t) random bits (ρ computable) read after the input, sound on every string, success on the stated fraction of strings; reason: the uniform measure on random strings; worst-case time on every string
--   - encoding: an integer budget b < n → b ∈ ℕ with b < n; reason: budgets are nonnegative integers (App. C, p.92)
--   - generalization: 'We assume that all input graphs have at least one edge' (§8.2, p.57) → every graph is admitted; reason: an algorithm on all graphs specializes to the graphs with an edge
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 8.6, p.59 (printed) = PDF p.61; App. C.3, p.93

import Mathlib
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_lam
import Definitions.Def_RevRedSAT_SearchWithin
import Definitions.Def_RevRedSAT_VCInstance
import Definitions.Def_RevRedSAT_Supplement_CountingDSAT
import Definitions.Def_RevRedSAT_Supplement_CVCValid

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **Theorem 8.6 (finding a connected dominating set).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 8.6, p.59: "Assume the Counting d-SAT Assumption. There is a randomized algorithm that
given an n-vertex graph G and an integer budget b < n, finds a connected dominating set of size at
most b, or reports NO, in time 2^{O(n·η(n)³/√λ(n))}. On a YES instance a set is returned with
probability at least 2/3; on a NO instance the algorithm always reports NO."

Under Assumption 4.5 there are a machine with finite alphabets and a constant `C` giving a Monte
Carlo search algorithm for Connected Dominating Set (`CDSValid`) on the codes of the instances
`(n, G, b)` with `b < n`, without false positives and with success probability at least `2/3`,
within `⌊2^{C·nη(n)³/√λ(n)}⌋` steps on every random string.

**Formalization Note** Budgets are nonnegative (App. C, p.92). With `b < n` the code has length
polynomial in `n`, so no input-length term is needed. Every graph is admitted, including
graphs with no edge, which §8.2 sets aside (p.57: "We assume that all input graphs have at least
one edge"). -/
theorem theorem_8_6 :
    CountingDSAT →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ C : ℝ,
        MonteCarloWithin M VCInstance.n (fun I w => I.k < I.n ∧ IsVCCode I w) CDSValid
          (fun I _ => ⌊(2 : ℝ) ^ (C * I.n * eta I.n ^ 3 / Real.sqrt (lam I.n))⌋₊)
          (2 / 3) := by sorry

end RevRedSAT.Supplement
