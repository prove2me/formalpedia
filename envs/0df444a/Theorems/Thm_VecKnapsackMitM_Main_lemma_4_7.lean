-- Prove2me | Theorems.Thm_VecKnapsackMitM_Main_lemma_4_7
-- name    : VecKnapsackMitM.Main.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:36:12.371312+00:00
-- url     : https://prove2.me/theorems/d57b2296-1633-429e-853c-3f0738da5b32
-- title:
--   Lemma 4.7 — Algorithm 3 runs in time $(n^{\lceil (d-1)/(2\varepsilon)-1/2+\rho\rceil}+n^d)(d\log n/(\rho\varepsilon))^{O(d)}$
-- statement:
--   There are one admissible deterministic real-RAM program and one absolute constant $C$ such that for every $d\ge2$, $\varepsilon,\rho\in(0,1)$ and every $d$-Knapsack instance with $n$ items (nonnegative data), the program, started on `knapsackInput`, halts within
--   $$\bigl(N^{\lceil \frac{d-1}{2\varepsilon}-\frac12+\rho\rceil}+N^d\bigr)\cdot\Bigl(\frac{d\log_2N}{\rho\varepsilon}\Bigr)^{C\cdot d},\qquad N=\max(n,2),$$
--   steps with every output cell $0$ or $1$, and the output set is a possible output of Algorithm 3 on $(I,\bar W,\varepsilon,\rho)$ (`Alg3Output`).
--
--   Differences from the source:
--   - encoding: items I = {1, …, n} and dimensions t ∈ {1, …, d} → items Fin n (the paper's item i+1 is i) and dimensions Fin d (the paper's dimension t+1 is t: w̄_1 is t = 0, w̄_d is t = d − 1, the middle dimensions 2, …, d − 1 are 1 ≤ t, t + 2 ≤ d); reason: zero-based finite indexing; same instances and same sets
--   - reading: n inside every bound with a log n factor → N = max(n, 2) (NN n); reason: log 1 = 0 makes the printed bounds 0 at n = 1, contradicting e.g. v_∅ ∈ L_1 (INSIGHTS I1); identical to the printed bound for n ≥ 2
--   - generalization: an algorithm on the RealRAM (§2, printed p. 8) → an admissible program (VecBalPoly.Admissible: rational literals, no √, no random draws) of the published unit-cost real RAM MatMulTimeLP, which has no floor, no real-to-index conversion and no index multiplication; time = executed instructions including the final halt; reason: fewer primitives only make the existential claim harder; every such program is a deterministic RealRAM algorithm with the same step count, so the Lean statement specializes to the paper's
--   - reading: "in time …^{O(d)}" for given parameters → one program P and one absolute constant C, chosen before d, the error parameters and the input; the O(d) exponent is C·d; reason: the bounds are stated for all d, so the constant in O(d) is absolute; one procedure taking the parameters as input is the stronger of the two readings and is what the paper describes
--   - encoding: the instance (I, W̄) and ε, ρ given to the algorithm; the returned set → input knapsackInput: N[0] = d, N[1] = n; R[0] = ε, R[1] = ρ, R[2 + t] = W̄_{t+1}, then p(i), w̄(i) item by item; output: every N[2 + i] (i < n) is 0 or 1 and the returned set is {i | N[2 + i] = 1}; reason: a machine statement needs a layout; requiring 0/1 cells makes the decoding unambiguous
--   - reading: "Algorithm 3 runs in time T" → a program halting within T whose output is a possible output of the Algorithm 3 specification (Alg3Output); reason: pseudocode with abstract subroutines (the ORS of Lemma 4.5, the lists of Lemma 4.2) is not a machine program; an implementation is a program whose outputs are the algorithm's outputs, and the time is that program's step count
--   - generalization: §2 assumes every item individually fits the capacities → all nonnegative instances, including individually infeasible items; reason: range queries reject every infeasible candidate; the proof uses only subsets of an optimal feasible solution, whose individual items fit
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; Lemma 4.7, printed p. 21 (PDF 22), proof printed pp. 21–22 (PDF 22–23)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine
import Definitions.Def_VecKnapsackMitM_Main_Algorithm3

namespace VecKnapsackMitM.Main

open MatMulTimeLP

/-- Bringmann, Kulik, Węgrzycki (2026), Lemma 4.7, printed p. 21 (PDF 22). There are one
admissible real-RAM program and one absolute constant `C` such that for every `d ≥ 2`,
`ε, ρ ∈ (0, 1)` and every nonnegative d-Knapsack instance, the program halts within
`(N^{⌈(d−1)/(2ε) − 1/2 + ρ⌉} + N^d) · (d log₂ N/(ρ ε))^{C d}` steps (`N = max(n, 2)`) with a 0/1
output that is a possible output of Algorithm 3 on `(I, W̄, ε, ρ)`. -/
theorem lemma_4_7 :
    ∃ P : Program, VecBalPoly.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d n : ℕ), 2 ≤ d → ∀ (ε ρ : ℝ), 0 < ε → ε < 1 → 0 < ρ → ρ < 1 →
        ∀ inst : Instance d n, inst.Nonneg →
          RunsWithin P (knapsackInput inst ε ρ) (mainBound d n ε ρ C)
            (fun s => OutputBinary s n ∧ Alg3Output inst ε ρ (outputSet s n)) := by sorry

end VecKnapsackMitM.Main
