-- Prove2me | Theorems.Thm_RevRedSAT_Supplement_theorem_10_1
-- name    : RevRedSAT.Supplement.theorem_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:05:55.491672+00:00
-- url     : https://prove2.me/theorems/bc116ee5-c9fa-45c5-b169-ba4cb9d7e92c
-- title:
--   Theorem 10.1 — MaxSAT in $2^{O(K\sqrt{\eta(K)}/\lambda(K)^{1/4})}|I|^{O(1)}$ and MaxSAT Above Half in the excess $k$
-- statement:
--   Assume the Clause-Based $d$-SAT Assumption 4.3.
--
--   1. There are a deterministic algorithm and constants $C,c$ that solve MaxSAT with absolute target $K$ — return an assignment satisfying at least $K$ clause occurrences, or report that none exists — within $\bigl\lfloor 2^{C\,K\sqrt{\eta(K)}/\lambda(K)^{1/4}}|w|^{c}\bigr\rfloor$ steps.
--   2. There are a deterministic algorithm and constants $C,c$ that solve MaxSAT Above Half with excess $k$ in the same sense (all $m$ clauses nonempty, target $\lceil m/2\rceil+k$) within $\bigl\lfloor 2^{C\,k\sqrt{\eta(k)}/\lambda(k)^{1/4}}|w|^{c}\bigr\rfloor$ steps.
--   3. There is an exponent $c$ such that for every fixed $d\ge1$ there are a deterministic algorithm and a constant $C_d$ that solve MaxSAT Above Half on formulas whose clauses have at most $d$ literals within
--   $$\Bigl\lfloor 2^{C_d\,k/\sqrt{\lambda(k)}}\,|w|^{c}\Bigr\rfloor$$
--   steps.
--
--   The excess parameterization measures the target above the guarantee $\lceil m/2\rceil$ of a random assignment, so the total target can be large while $k$ is small.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: a returned truth assignment → the set of its variables set to one (assignOf), output with the published search notion SearchWithin; reason: every assignment is determined by its set of ones; "solved" is the search problem of §10, p.76: 'We seek a truth assignment satisfying at least K clauses, or determine that none exists'
--   - reading: |I|^{O(1)} in the fixed-width clause → one exponent c for every d ≥ 1, chosen before d; reason: an unsubscripted O is absolute (§3, p.27); only the constant is O_d
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 10.1, p.76 (printed) = PDF p.78; App. C.5, pp.94–95

import Mathlib
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_lam
import Definitions.Def_RevRedSAT_encCNF
import Definitions.Def_RevRedSAT_Supplement_ClauseBasedDSAT
import Definitions.Def_RevRedSAT_SearchWithin
import Definitions.Def_RevRedSAT_Supplement_SATInstance

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **Theorem 10.1 (MaxSAT and MaxSAT Above Half).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 10.1, p.76: "Assume the Clause-Based d-SAT Assumption (Assumption 4.3). Then,
1. MaxSAT, parameterized by the total target K, can be solved in time 2^{O(K√η(K)/λ(K)^{1/4})}
|I|^{O(1)}. 2. MaxSAT Above Half, parameterized by the excess k above ⌈m/2⌉, can be solved in time
2^{O(k√η(k)/λ(k)^{1/4})} |I|^{O(1)}. For every fixed integer d ≥ 1, if each clause contains at most
d literals, the running time improves to 2^{O_d(k/√λ(k))}|I|^{O(1)}."

Under Assumption 4.3:
1. a machine with finite alphabets solves MaxSAT with absolute target `K` (`MaxSATValid`): it
   outputs `[false]` when no assignment has score at least `K`, and otherwise `true` followed by
   the set of variables of such an assignment set to one, within
   `⌊2^{C·K√η(K)/λ(K)^{1/4}} · |w|^c⌋` steps;
2. a machine solves MaxSAT Above Half with excess `k` (`AboveHalfValid`, all clauses nonempty) in
   the same sense within `⌊2^{C·k√η(k)/λ(k)^{1/4}} · |w|^c⌋` steps;
3. there is one exponent `c` such that for every `d ≥ 1` a machine solves MaxSAT Above Half on
   formulas of width at most `d` within `⌊2^{C_d·k/√λ(k)} · |w|^c⌋` steps.

**Formalization Note** "Solved" is the search problem of §10 (p.76: "We seek a truth assignment
satisfying at least K clauses, or determine that none exists"), with the published search notion
`RevRedSAT.SearchWithin`; an assignment is returned as its set of ones (`assignOf`). The
polynomial exponent of clause 3 is absolute (unsubscripted `O(1)`), the constant `C_d` depends on
`d`. Width counts distinct literals. -/
theorem theorem_10_1 :
    ClauseBasedDSAT →
      (∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ (C : ℝ) (c : ℕ),
        SearchWithin M SATInstance.n IsSATCode MaxSATValid
          (fun I w => expBound (C * I.k * Real.sqrt (eta I.k) / lam I.k ^ ((1 : ℝ) / 4))
            w.length c)) ∧
      (∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ (C : ℝ) (c : ℕ),
        SearchWithin M SATInstance.n IsAboveHalfCode AboveHalfValid
          (fun I w => expBound (C * I.k * Real.sqrt (eta I.k) / lam I.k ^ ((1 : ℝ) / 4))
            w.length c)) ∧
      (∃ c : ℕ, ∀ d : ℕ, 1 ≤ d →
        ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ C : ℝ,
          SearchWithin M SATInstance.n (fun I w => width I.φ ≤ d ∧ IsAboveHalfCode I w)
            AboveHalfValid
            (fun I w => expBound (C * I.k / Real.sqrt (lam I.k)) w.length c)) := by sorry

end RevRedSAT.Supplement
