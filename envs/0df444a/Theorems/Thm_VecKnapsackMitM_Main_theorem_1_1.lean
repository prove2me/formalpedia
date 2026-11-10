-- Prove2me | Theorems.Thm_VecKnapsackMitM_Main_theorem_1_1
-- name    : VecKnapsackMitM.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:34:06.695312+00:00
-- url     : https://prove2.me/theorems/d484ec4c-66fc-4893-a84f-4635f46e7c77
-- title:
--   Theorem 1.1 — $(1-\varepsilon)$-approximate $d$-Knapsack in time $(n^{\lceil (d-1)/(2\varepsilon)-1/2+\rho\rceil}+n^d)(d\log n/(\rho\varepsilon))^{O(d)}$
-- statement:
--   There are one admissible deterministic real-RAM program $P$ and one absolute constant $C$, fixed before $d$, $\varepsilon$, $\rho$ and the instance, such that for every $d\ge2$, $\varepsilon,\rho\in(0,1)$ and every $d$-Knapsack instance with $n$ items (nonnegative real profits, weight vectors and capacities; no sortedness, no $\bar w(i)\le\bar W$, $n=0$ allowed), $P$ started on `knapsackInput` halts within
--   $$\bigl(N^{\lceil \frac{d-1}{2\varepsilon}-\frac12+\rho\rceil}+N^d\bigr)\cdot\Bigl(\frac{d\log_2N}{\rho\varepsilon}\Bigr)^{C\cdot d},\qquad N=\max(n,2),$$
--   steps with every output cell $0$ or $1$, and the output set $S$ is feasible with $p(S)\ge(1-\varepsilon)\,\mathrm{OPT}$.
--
--   Differences from the source:
--   - encoding: items I = {1, …, n} and dimensions t ∈ {1, …, d} → items Fin n (the paper's item i+1 is i) and dimensions Fin d (the paper's dimension t+1 is t: w̄_1 is t = 0, w̄_d is t = d − 1, the middle dimensions 2, …, d − 1 are 1 ≤ t, t + 2 ≤ d); reason: zero-based finite indexing; same instances and same sets
--   - reading: n inside every bound with a log n factor → N = max(n, 2) (NN n); reason: log 1 = 0 makes the printed bounds 0 at n = 1, contradicting e.g. v_∅ ∈ L_1 (INSIGHTS I1); identical to the printed bound for n ≥ 2
--   - generalization: an algorithm on the RealRAM (§2, printed p. 8) → an admissible program (VecBalPoly.Admissible: rational literals, no √, no random draws) of the published unit-cost real RAM MatMulTimeLP, which has no floor, no real-to-index conversion and no index multiplication; time = executed instructions including the final halt; reason: fewer primitives only make the existential claim harder; every such program is a deterministic RealRAM algorithm with the same step count, so the Lean statement specializes to the paper's
--   - reading: "in time …^{O(d)}" for given parameters → one program P and one absolute constant C, chosen before d, the error parameters and the input; the O(d) exponent is C·d; reason: the bounds are stated for all d, so the constant in O(d) is absolute; one procedure taking the parameters as input is the stronger of the two readings and is what the paper describes
--   - encoding: the instance (I, W̄) and ε, ρ given to the algorithm; the returned set → input knapsackInput: N[0] = d, N[1] = n; R[0] = ε, R[1] = ρ, R[2 + t] = W̄_{t+1}, then p(i), w̄(i) item by item; output: every N[2 + i] (i < n) is 0 or 1 and the returned set is {i | N[2 + i] = 1}; reason: a machine statement needs a layout; requiring 0/1 cells makes the decoding unambiguous
--   - encoding: p(S) ≥ (1 − ε)·OPT, OPT an optimal solution → IsApprox: S feasible and (1 − ε)·p(S') ≤ p(S) for every feasible S'; reason: OPT attains the maximum over the finitely many feasible sets; equivalent
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; Theorem 1.1, printed p. 2 (PDF 3), restated with proof printed p. 22 (PDF 23)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine

namespace VecKnapsackMitM.Main

open MatMulTimeLP

/-- Bringmann, Kulik, Węgrzycki (2026), Theorem 1.1, printed p. 2 (PDF 3), restated with proof
printed p. 22 (PDF 23). Given any `d ≥ 2` and `ε, ρ ∈ (0, 1)`, d-Knapsack has a
`(1 − ε)`-approximation algorithm with running time
`(n^{⌈(d−1)/(2ε) − 1/2 + ρ⌉} + n^d) · (d log n/(ρ·ε))^{O(d)}`: one admissible deterministic
real-RAM program and one absolute constant `C`, fixed before `d`, `ε`, `ρ` and the instance,
such that on every nonnegative instance the program halts within
`(N^{⌈(d−1)/(2ε) − 1/2 + ρ⌉} + N^d) · (d log₂ N/(ρ ε))^{C d}` steps (`N = max(n, 2)`) with every
output cell `0` or `1`, and the output set is feasible with profit at least `(1 − ε) · OPT`. -/
theorem theorem_1_1 :
    ∃ P : Program, VecBalPoly.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d n : ℕ), 2 ≤ d → ∀ (ε ρ : ℝ), 0 < ε → ε < 1 → 0 < ρ → ρ < 1 →
        ∀ inst : Instance d n, inst.Nonneg →
          RunsWithin P (knapsackInput inst ε ρ) (mainBound d n ε ρ C)
            (fun s => OutputBinary s n ∧ inst.IsApprox ε (outputSet s n)) := by sorry

end VecKnapsackMitM.Main
