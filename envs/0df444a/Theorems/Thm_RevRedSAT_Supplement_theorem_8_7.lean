-- Prove2me | Theorems.Thm_RevRedSAT_Supplement_theorem_8_7
-- name    : RevRedSAT.Supplement.theorem_8_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:04:33.707493+00:00
-- url     : https://prove2.me/theorems/a90e81fc-ca16-44de-9d53-d755d58c73ab
-- title:
--   Theorem 8.7 — Max Leaf Spanning Tree in $2^{O(k\eta(k)^3/\sqrt{\lambda(k)})}\mathrm{poly}(n)$, success 2/3
-- statement:
--   Assume the Counting $d$-SAT Assumption 4.5. There are a randomized algorithm and constants $C,c$ that, on an $n$-vertex graph $G$ and a leaf target $k$, decide whether $G$ has a spanning tree with at least $k$ leaves and return such a tree (as its edge list), within
--
--   $$\Bigl\lfloor 2^{C\,k\eta(k)^3/\sqrt{\lambda(k)}}\,(n+2)^{c}\Bigr\rfloor$$
--
--   steps on every random string. On a YES instance it returns a valid tree with probability at least $2/3$; on a NO instance it always reports NO.
--
--   The parameter is the number of leaves, not the graph order.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: a randomized algorithm with no false positives and the stated success probability → MonteCarloWithin (EdgeMonteCarloWithin for edge-set solutions): ρ(t) random bits (ρ computable) read after the input, sound on every string, success on the stated fraction of strings; reason: the uniform measure on random strings; worst-case time on every string
--   - encoding: poly(n) → (n + 2)^c; reason: a polynomial in n that is positive at n = 0
--   - reading: spanning tree of an n-vertex graph (App. C.4 says nothing about n = 0) → the graph with no vertices has no spanning tree; reason: Mathlib's trees are nonempty; App. C.4: a disconnected nonempty graph has no spanning tree
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 8.7, p.61 (printed) = PDF p.63; App. C.4, p.94

import Mathlib
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_lam
import Definitions.Def_RevRedSAT_VCInstance
import Definitions.Def_RevRedSAT_Supplement_CountingDSAT
import Definitions.Def_RevRedSAT_Supplement_SteinerInstance
import Definitions.Def_RevRedSAT_Supplement_EdgeMonteCarloWithin

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **Theorem 8.7 (Max Leaf Spanning Tree by the leaf target).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 8.7, p.61: "Assume the Counting d-SAT Assumption. On an n-vertex graph, one can decide
whether a spanning tree with at least k leaves exists, and recover such a tree, by a randomized
algorithm in time 2^{O(kη(k)³/√λ(k))} poly(n). On a YES instance the algorithm returns a valid tree
with probability at least 2/3; on a NO instance it always reports NO."

Under Assumption 4.5 there are a machine with finite alphabets and constants `C, c` giving a Monte
Carlo algorithm on the codes of `(n, G, k)` (`RevRedSAT.IsVCCode`, `k` last) that outputs `[false]`
or `true` followed by the edge list of a spanning tree of `G` with at least `k` leaves
(`MaxLeafValid`), never a false positive, with success probability at least `2/3` on YES instances,
within `⌊2^{C·kη(k)³/√λ(k)} · (n + 2)^c⌋` steps on every random string.

**Formalization Note** `poly(n)` is `(n + 2)^c`; the code has length polynomial in `n` plus
`O(log k)`, absorbed by the bound. -/
theorem theorem_8_7 :
    CountingDSAT →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ (C : ℝ) (c : ℕ),
        EdgeMonteCarloWithin M VCInstance.n IsVCCode MaxLeafValid
          (fun I _ => expBound (C * I.k * eta I.k ^ 3 / Real.sqrt (lam I.k)) (I.n + 2) c)
          (2 / 3) := by sorry

end RevRedSAT.Supplement
