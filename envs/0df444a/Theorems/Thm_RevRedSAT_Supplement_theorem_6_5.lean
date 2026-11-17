-- Prove2me | Theorems.Thm_RevRedSAT_Supplement_theorem_6_5
-- name    : RevRedSAT.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:00:22.294562+00:00
-- url     : https://prove2.me/theorems/9be03d31-4e46-4ab2-8255-65168717248e
-- title:
--   Theorem 6.5 — d-Hitting Set in $2^{O_d(k/\lambda(k)^{1/(8d-6)})}|I|^{O_d(1)}$ under Clause-Based d-SAT
-- statement:
--   Let $\lambda(t)=\log_2(t+2)$ and fix $d\ge2$.
--
--   1. Under the Clause-Based $d$-SAT Assumption 4.3 there are a deterministic algorithm and constants $C_d,c_d$ that decide whether a family of sets of size at most $d$ has a hitting set of size at most $k$, and output one if it exists, within
--   $$\Bigl\lfloor 2^{C_d\,k/\lambda(k)^{1/(8d-6)}}\,|w|^{c_d}\Bigr\rfloor$$
--   steps on every code $w$.
--   2. The same conclusion holds under the Quantitative $d$-SAT Assumption 4.2.
--
--   Only the clause-based bound is used, so the theorem needs the weaker assumption.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.5, p.40 (printed) = PDF p.42

import Mathlib
import Definitions.Def_RevRedSAT_QuantDSAT
import Definitions.Def_RevRedSAT_IsHSCode
import Definitions.Def_RevRedSAT_Supplement_ClauseBasedDSAT

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **Theorem 6.5 (d-Hitting Set under the Clause-Based d-SAT Assumption).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.5, p.40: "For every fixed d ≥ 2, under the Clause-Based d-SAT Assumption one can
decide whether a rank-d family has a hitting set of size at most k, and find one if it exists,
deterministically in time 2^{O_d(k/λ(k)^{1/(8d−6)})}|I|^{O_d(1)}. In particular, the same conclusion
holds under the Quantitative d-SAT Assumption."

1. Under Assumption 4.3, for every `d ≥ 2` a machine with finite alphabets solves the `d`-Hitting
   Set search problem within `⌊2^{C_d·k/λ(k)^{1/(8d−6)}} · |w|^{c_d}⌋` steps.
2. The same under Assumption 4.2.

**Formalization Note** Search output as in the published `RevRedSAT.SearchWithin`; the exponent
`1/(8d − 6)` is a real power. The constant and the polynomial exponent depend on `d`
(`O_d`). -/
theorem theorem_6_5 :
    (ClauseBasedDSAT → ∀ d : ℕ, 2 ≤ d →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ (C : ℝ) (c : ℕ),
        SearchWithin M HSElemKernel.HSInstance.n (IsDHSCode d) HSValid
          (fun I w => expBound (C * I.k / lam I.k ^ ((1 : ℝ) / (8 * (d : ℝ) - 6))) w.length c)) ∧
    (QuantDSAT → ∀ d : ℕ, 2 ≤ d →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ (C : ℝ) (c : ℕ),
        SearchWithin M HSElemKernel.HSInstance.n (IsDHSCode d) HSValid
          (fun I w => expBound (C * I.k / lam I.k ^ ((1 : ℝ) / (8 * (d : ℝ) - 6))) w.length c)) := by sorry

end RevRedSAT.Supplement
