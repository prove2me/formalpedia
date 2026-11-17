-- Prove2me | Theorems.Thm_RevRedSAT_Supplement_theorem_2_5
-- name    : RevRedSAT.Supplement.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:05:14.009104+00:00
-- url     : https://prove2.me/theorems/18ce1f46-b4e7-4b99-b69d-ee981e2e5a41
-- title:
--   Theorem 2.5 — randomized Feedback Vertex Set in $2^{O(kL_2^{1/9}/L^{1/54})}|I|^{O(1)}$, success 2/3
-- statement:
--   Assume the Counting $d$-SAT Assumption 4.5. Let $L=\log_2(k+2)$ and $L_2=\log_2(L+2)$. There are a randomized algorithm and constants $C,c$ that, given a finite simple undirected graph $G$ and a budget $k$, either output a feedback vertex set of size at most $k$ or return NO, within
--
--   $$\Bigl\lfloor 2^{C\,kL_2^{1/9}/L^{1/54}}\,|w|^{c}\Bigr\rfloor$$
--
--   steps on every random string. On every YES instance it outputs such a set with probability at least $2/3$; on every NO instance it always returns NO.
--
--   Since $L_2^{1/9}/L^{1/54}\to0$, this is a $2^{o(k)}|I|^{O(1)}$ algorithm for Feedback Vertex Set.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: a randomized algorithm with no false positives and the stated success probability → MonteCarloWithin (EdgeMonteCarloWithin for edge-set solutions): ρ(t) random bits (ρ computable) read after the input, sound on every string, success on the stated fraction of strings; reason: the uniform measure on random strings; worst-case time on every string
--   - encoding: time 2^{O(kL2^{1/9}/L^{1/54})}|I|^{O(1)} = 2^{o(k)}|I|^{O(1)} → the explicit bound only; reason: the second form is implied by the first, since L₂^{1/9}/L^{1/54} → 0
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 2.5, p.62 (printed) = PDF p.64 (first stated on p.17); App. C.4, p.94

import Mathlib
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_lam
import Definitions.Def_RevRedSAT_SearchWithin
import Definitions.Def_RevRedSAT_VCInstance
import Definitions.Def_RevRedSAT_Supplement_CountingDSAT
import Definitions.Def_RevRedSAT_Supplement_CVCValid

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **Theorem 2.5 (randomized Feedback Vertex Set via counting).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 2.5, p.62 (first stated on p.17): "Assume the Counting d-SAT Assumption. There is a
randomized algorithm that, given an instance I = (G, k) of Feedback Vertex Set on a finite simple
undirected graph, runs in time 2^{O(kL2^{1/9}/L^{1/54})}|I|^{O(1)} = 2^{o(k)}|I|^{O(1)}, where
L = log2(k + 2) and L2 = log2(L + 2), and either outputs a feedback vertex set of size at most k or
returns NO. On every YES instance, it outputs such a set with probability at least 2/3; on every NO
instance, it always returns NO."

Under Assumption 4.5 there are a machine with finite alphabets and constants `C, c` giving a Monte
Carlo search algorithm for Feedback Vertex Set (`FVSValid`, codes `RevRedSAT.IsVCCode`), without
false positives and with success probability at least `2/3`, within
`⌊2^{C·k·L₂^{1/9}/L^{1/54}} · |w|^c⌋` steps, `L = λ(k) = log₂(k + 2)`, `L₂ = log₂(L + 2)`.

**Formalization Note** `L₂` is `log₂(λ(k) + 2)`, not `η(k)`. The equality with `2^{o(k)}|I|^{O(1)}`
is a consequence of the explicit bound (`L₂^{1/9}/L^{1/54} → 0`) and is not stated separately. -/
theorem theorem_2_5 :
    CountingDSAT →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ (C : ℝ) (c : ℕ),
        MonteCarloWithin M VCInstance.n IsVCCode FVSValid
          (fun I w => expBound (C * I.k * Real.logb 2 (lam I.k + 2) ^ ((1 : ℝ) / 9) /
            lam I.k ^ ((1 : ℝ) / 54)) w.length c) (2 / 3) := by sorry

end RevRedSAT.Supplement
