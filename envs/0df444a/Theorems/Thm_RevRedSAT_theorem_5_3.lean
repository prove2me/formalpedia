-- Prove2me | Theorems.Thm_RevRedSAT_theorem_5_3
-- name    : RevRedSAT.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:57.606762+00:00
-- url     : https://prove2.me/theorems/f029b5ff-4c0b-48f7-9e4a-fe06bdcab671
-- title:
--   Theorem 5.3 — Vertex Cover in $2^{O(k\eta(k)/\sqrt{\lambda(k)})}|I|^{O(1)}$ and $2^{o(k)}|I|^{O(1)}$
-- statement:
--   1. Under the Quantitative $d$-SAT Assumption (4.2), there are a machine with finite alphabets and constants $C,c$ that solve the Vertex Cover search problem (decide, and find a cover of size at most $k$ whenever one exists) on every code $w$ of every instance within
--
--   $$\bigl\lfloor 2^{C\,k\eta(k)/\sqrt{\lambda(k)}}\;|w|^{c}\bigr\rfloor\ \text{steps}.$$
--
--   2. Under the Subexponential 3-SAT Assumption (4.1), there are such a machine, an exponent $c$ and a function $g$ with $g(k)/k\to0$ that solve it within $2^{g(k)}|w|^c$ steps.
--
--   This is the Vertex Cover half of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - reading: an algorithm for the problem (Table 1: 'Det.; search') → a search algorithm: output 'no' exactly on NO-instances, otherwise the list of a feasible solution; reason: Table 1, App. C and the proofs (solution recovery) state search; the decision-only reading is weaker
--   - encoding: 2^{o(k)} → 2^{g(k)} for one g : ℕ → ℕ with g(k)/k → 0, chosen with the machine before the instance; reason: the definition of o(k); no rate of convergence is asked
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 5.3, p.36 (printed) = PDF p.38

import Mathlib
import Definitions.Def_RevRedSAT_SubexpThreeSAT
import Definitions.Def_RevRedSAT_QuantDSAT
import Definitions.Def_RevRedSAT_VCInstance

set_option autoImplicit false

namespace RevRedSAT

open Filter Topology

/-- **Theorem 5.3 (Vertex Cover under the SAT assumptions).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 5.3, p.36: "Under the Quantitative d-SAT Assumption (Assumption 4.2), Vertex Cover
can be decided, and a cover of size at most k found whenever one exists, deterministically in time
2^{O(kη(k)/√λ(k))}|I|^{O(1)}. Under the Subexponential 3-SAT Assumption (Assumption 4.1), the
running time is 2^{o(k)}|I|^{O(1)}."

**Formalization Note** Search output and machine model as in `theorem_1_1`; `2^{O(·)}|I|^{O(1)}` is
`⌊2^{C·kη(k)/√λ(k)}·|w|^c⌋` with `C`, `c` chosen with the machine, and `2^{o(k)}` is `2^{g(k)}`,
`g(k)/k → 0`. -/
theorem theorem_5_3 :
    (QuantDSAT →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
        ∃ (C : ℝ) (c : ℕ),
          SearchWithin M VCInstance.n IsVCCode VCValid
            (fun I w => expBound (vcRate C I.k) w.length c)) ∧
    (SubexpThreeSAT →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
        ∃ (c : ℕ) (g : ℕ → ℕ), Tendsto (fun k => (g k : ℝ) / k) atTop (𝓝 0) ∧
          SearchWithin M VCInstance.n IsVCCode VCValid
            (fun I w => 2 ^ g I.k * w.length ^ c)) := by sorry

end RevRedSAT
