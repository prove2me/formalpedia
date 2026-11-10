-- Prove2me | Theorems.Thm_RevRedSAT_theorem_6_7
-- name    : RevRedSAT.theorem_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:58.287485+00:00
-- url     : https://prove2.me/theorems/f5a708b3-cff1-4d6b-a0b9-68159cdd1ada
-- title:
--   Theorem 6.7 — d-Hitting Set in $2^{o(k)}|I|^{O(1)}$ under Subexponential 3-SAT
-- statement:
--   Assume the Subexponential 3-SAT Assumption (4.1). There is an exponent $c$ such that for every fixed $d\ge2$ there are a machine with finite alphabets and a function $g$ with $g(k)/k\to0$ that decide whether a $d$-Hitting Set instance has a hitting set of size at most $k$, and find one if it exists, within
--
--   $$2^{g(k)}\,|w|^{c}\ \text{steps}$$
--
--   on every code $w$.
--
--   This answers the qualitative question of the paper for $d$-Hitting Set, by sparsification and Lemma A.2.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - reading: an algorithm for the problem (Table 1: 'Det.; search') → a search algorithm: output 'no' exactly on NO-instances, otherwise the list of a feasible solution; reason: Table 1, App. C and the proofs (solution recovery) state search; the decision-only reading is weaker
--   - encoding: 2^{o(k)} → 2^{g(k)} for one g : ℕ → ℕ with g(k)/k → 0, chosen with the machine before the instance; reason: the definition of o(k); no rate of convergence is asked
--   - reading: |I|^{O(1)} → one exponent c for every d ≥ 2, chosen before d; reason: an unsubscripted O is absolute (§3, p.27); Theorems 6.7, 6.13 and Lemma 6.6 say the exponent is absolute
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.7, p.41 (printed) = PDF p.43

import Mathlib
import Definitions.Def_RevRedSAT_SubexpThreeSAT
import Definitions.Def_RevRedSAT_IsHSCode

set_option autoImplicit false

namespace RevRedSAT

open Filter Topology

/-- **Theorem 6.7 (d-Hitting Set in 2^{o(k)}|I|^{O(1)} under Assumption 4.1).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.7, p.41: "Under the Subexponential 3-SAT Assumption, for every fixed d ≥ 2 there is
a deterministic algorithm that decides whether a d-Hitting Set instance has a hitting set of size at
most k and finds one if it exists, in time 2^{o(k)}|I|^{O(1)}."

**Formalization Note** One polynomial exponent `c` for every `d` (an unsubscripted `O(1)`, §3; the
proof's preprocessing has "an absolute exponent on |I|", Lemma 6.6); the machine and the function
`g` with `g(k)/k → 0` depend on `d`. Search output as in `theorem_1_1`. -/
theorem theorem_6_7 :
    SubexpThreeSAT →
      ∃ c : ℕ, ∀ d : ℕ, 2 ≤ d →
        ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
          ∃ g : ℕ → ℕ, Tendsto (fun k => (g k : ℝ) / k) atTop (𝓝 0) ∧
            SearchWithin M HSElemKernel.HSInstance.n (IsDHSCode d) HSValid
              (fun I w => 2 ^ g I.k * w.length ^ c) := by sorry

end RevRedSAT
