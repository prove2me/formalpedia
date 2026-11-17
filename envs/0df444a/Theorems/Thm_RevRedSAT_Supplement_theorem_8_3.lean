-- Prove2me | Theorems.Thm_RevRedSAT_Supplement_theorem_8_3
-- name    : RevRedSAT.Supplement.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:03:14.773343+00:00
-- url     : https://prove2.me/theorems/c06301ad-969b-4394-9b59-633af312e0bf
-- title:
--   Theorem 8.3 — Steiner Tree, Connected Vertex Cover and Connected Dominating Set in $2^{O(n\eta(n)^3/\sqrt{\lambda(n)})}$, success 2/3
-- statement:
--   Assume the Counting $d$-SAT Assumption 4.5, and let $n$ be the number of vertices of the input graph. Each of the following problems has a randomized algorithm, with a constant $C$, that runs within
--
--   $$\Bigl\lfloor 2^{C\,n\eta(n)^3/\sqrt{\lambda(n)}}+C\,|w|\Bigr\rfloor$$
--
--   steps on every code $w$ and every random string, returns a valid solution with probability at least $2/3$ on a YES instance, and always reports NO on a NO instance:
--
--   1. unweighted Steiner Tree (a tree subgraph with at most $b$ edges containing every terminal);
--   2. Connected Vertex Cover with budget $b$;
--   3. Connected Dominating Set with budget $b$.
--
--   The exponent is measured in the graph order $n$, not in the solution size; for Connected Vertex Cover parameterized by the solution size, Theorem 5.5 is the barrier.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: a randomized algorithm with no false positives and the stated success probability → MonteCarloWithin (EdgeMonteCarloWithin for edge-set solutions): ρ(t) random bits (ρ computable) read after the input, sound on every string, success on the stated fraction of strings; reason: the uniform measure on random strings; worst-case time on every string
--   - reading: time 2^{O(nη(n)³/√λ(n))}, with a budget given in binary and unbounded → ⌊2^{C·nη(n)³/√λ(n)} + C·|w|⌋ steps; reason: a Mathlib TM2 machine halts only with every non-output stack empty, so it spends steps linear in |w|, and an arbitrary binary budget makes |w| larger than any function of the measure; the extra term only pays for reading the input and is absorbed by the exponential whenever the budget is at most exponential in the measure
--   - generalization: 'We assume that all input graphs have at least one edge and |R| ≥ 2 for Steiner Tree' (p.57) → every instance of App. C.3 is admitted; reason: an algorithm on all instances specializes to the restricted ones
--   - encoding: a tree subgraph of G → its edge set T, with vertex set R ∪ V(T); the empty solution when R = ∅; reason: a tree subgraph with at least one edge is determined by its edges; the only edgeless trees are single vertices, needed only when |R| ≤ 1
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 8.3, p.57 (printed) = PDF p.59; App. C.3, pp.93–94

import Mathlib
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_lam
import Definitions.Def_RevRedSAT_SearchWithin
import Definitions.Def_RevRedSAT_VCInstance
import Definitions.Def_RevRedSAT_Supplement_CountingDSAT
import Definitions.Def_RevRedSAT_Supplement_CVCValid
import Definitions.Def_RevRedSAT_Supplement_SteinerInstance
import Definitions.Def_RevRedSAT_Supplement_EdgeMonteCarloWithin

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **Theorem 8.3 (Steiner Tree, Connected Vertex Cover and Connected Dominating Set by n).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 8.3, p.57: "Assume the Counting d-SAT Assumption. Unweighted Steiner Tree, Connected
Vertex Cover, and Connected Dominating Set admit randomized algorithms with running time
2^{O(n·η(n)³/√λ(n))}, where n is the number of vertices in the input graph. On a YES instance, each
algorithm returns a valid solution with probability at least 2/3; on a NO instance it always
reports NO."

Under Assumption 4.5, for each of the three problems there are a machine with finite alphabets and a
constant `C` giving a Monte Carlo search algorithm without false positives and with success
probability at least `2/3`, within `⌊2^{C·nη(n)³/√λ(n)} + C·|w|⌋` steps on every random string:
1. Steiner Tree (solutions are edge sets, `EdgeMonteCarloWithin`);
2. Connected Vertex Cover (`CVCValid`, codes `RevRedSAT.IsVCCode`, budget last);
3. Connected Dominating Set (`CDSValid`, same codes).

**Formalization Note** Every instance is admitted, including graphs with no edge and Steiner
instances with `|R| < 2`, which p.57 sets aside ("We assume that all input graphs have at least one
edge and |R| ≥ 2 for Steiner Tree") and App. C.3 defines. The additive `C·|w|` pays for erasing the
input (Mathlib's TM2 halts with empty non-output stacks), which an unbounded binary budget makes
longer than any function of `n`. -/
theorem theorem_8_3 :
    CountingDSAT →
      (∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ C : ℝ,
        EdgeMonteCarloWithin M SteinerInstance.n IsSteinerCode SteinerValid
          (fun I w => ⌊(2 : ℝ) ^ (C * I.n * eta I.n ^ 3 / Real.sqrt (lam I.n)) +
            C * w.length⌋₊) (2 / 3)) ∧
      (∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ C : ℝ,
        MonteCarloWithin M VCInstance.n IsVCCode CVCValid
          (fun I w => ⌊(2 : ℝ) ^ (C * I.n * eta I.n ^ 3 / Real.sqrt (lam I.n)) +
            C * w.length⌋₊) (2 / 3)) ∧
      (∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ C : ℝ,
        MonteCarloWithin M VCInstance.n IsVCCode CDSValid
          (fun I w => ⌊(2 : ℝ) ^ (C * I.n * eta I.n ^ 3 / Real.sqrt (lam I.n)) +
            C * w.length⌋₊) (2 / 3)) := by sorry

end RevRedSAT.Supplement
