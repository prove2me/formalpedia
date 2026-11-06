-- Prove2me | Theorems.Thm_RandomLPIPM_lemma_8_13
-- name    : RandomLPIPM.lemma_8_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:53.808207+00:00
-- url     : https://prove2.me/theorems/03f516f7-e692-47ac-8d20-1c381c51be07
-- title:
--   Lemma 8.13 — near the central path at $\mu\le m_*^2/(8n^2)$, $\min_{B^*}x_i\ge5\max_{N^*}x_j$
-- statement:
--   Consider a linear program in the form (LP), with no rank condition on $A$ and the dual program strictly feasible. Let $(x^*,y^*,s^*)$ be an optimal primal-dual solution, $B^*=\operatorname{supp}(x^*)$, $N^*=\operatorname{supp}(s^*)$, and let $m>0$ be a lower bound on every positive coordinate of $(x^*,s^*)$ (for instance $m=m_*=\min\{\min_{B^*}x^*_i,\min_{N^*}s^*_j\}$). Then for every $\mu\in(0,m^2/(8n^2)]$ and every strictly feasible $x$ with $E_\mu(x)\le1/6$,
--   $$x_i\ge 5\,x_j\qquad\text{for all } i\in B^*,\ j\in N^*,$$
--   that is, $\min_{i\in B^*}x_i/\max_{j\in N^*}x_j\ge5$.
--
--   So the large coordinates of an approximate central point at small $\mu$ reveal the optimal basis.
--
--   Differences from the source:
--   - generalization: m* = min{min_{B*} x*_i, min_{N*} s*_j} and (B*, N*) the optimal basis → any m > 0 below every positive coordinate of (x*, s*); B* = supp x*, N* = supp s* with no basis/partition assumption; reason: the proof uses only these two facts; m = m* and a strictly complementary optimum is the printed case
--   - encoding: min_{i∈B*} x_i / max_{j∈N*} x_j ≥ 5 → 5·x_j ≤ x_i for all i ∈ B*, j ∈ N*; reason: equal when both sets are nonempty, and well defined when one is empty
--   - generalization: a general linear program, (LP) of p.4 having A of full row rank → no rank hypothesis on A; reason: the proof (Proposition 8.12, p.74) uses only the central path equations and feasibility, and the central point exists for any rank; (LP) is an instance
--   - encoding: a central path point of the program exists → dual strictly feasible as a hypothesis; primal strict feasibility comes from x; reason: the condition under which the barrier minimizer exists
--   - reading: the unsubscripted norm of E_μ (p.73) → the Euclidean norm; reason: Theorem 2.1 and Remark 1.2 write ‖·‖₂, and the proofs of Lemmas 9.5 and 9.7 use ℓ2
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 8.13, p.74

import Mathlib
import Definitions.Def_RandomLPIPM_IsPrimalStrictFeas
import Definitions.Def_RandomLPIPM_IsDualStrictFeas
import Definitions.Def_RandomLPIPM_IsPDOptimal
import Definitions.Def_RandomLPIPM_proximity

open Matrix

namespace RandomLPIPM

/-- **Lemma 8.13 (basis identification from an approximate central point).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 8.13, p.74.

For a general linear program, let `(x*, s*)` be a primal-dual optimal solution with `(B*, N*)` the
corresponding optimal basis and `m* = min{min_{i∈B*} x*ᵢ, min_{j∈N*} s*ⱼ}`. Then for any
`μ ∈ (0, m*²/(8n²)]` and any strictly feasible primal `x` with `E_μ(x) ≤ 1/6`,
`min_{i∈B*} xᵢ / max_{j∈N*} xⱼ ≥ 5`.

**Formalization Note.** "General linear program": `(A, b, c)` with a central path, i.e. dual strictly
feasible (hypothesis `hD`) and primal strictly feasible (supplied by `x`); no rank condition is needed,
so the full-row-rank pair (LP) of p.4 is an instance. `E_μ` uses `x_μ = centralX`, Euclidean norm.
`B* = supp(x*)`, `N* = supp(s*)`. The ratio is stated in multiplied form `5xⱼ ≤ xᵢ` for every
`i ∈ B*`, `j ∈ N*` (equal to the ratio form when both sets are nonempty). Instead of `m*` itself the
statement takes any `m > 0` bounding every positive coordinate of `(x*, s*)` from below, and it
does not assume that `(B*, N*)` partitions `[n]`; with `m = m*` and a strictly complementary
optimum it is the printed lemma. -/
theorem lemma_8_13 {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ) (c : Fin n → ℝ)
    (hD : ∃ y, IsDualStrictFeas A c y)
    (xs : Fin n → ℝ) (ys : Fin d → ℝ) (ss : Fin n → ℝ) (hopt : IsPDOptimal A b c xs ys ss)
    (m : ℝ) (hm : 0 < m) (hmx : ∀ i, 0 < xs i → m ≤ xs i) (hms : ∀ j, 0 < ss j → m ≤ ss j)
    (μ : ℝ) (hμ : 0 < μ) (hμm : μ ≤ m ^ 2 / (8 * (n : ℝ) ^ 2))
    (x : Fin n → ℝ) (hx : IsPrimalStrictFeas A b x) (hE : proximity A b c μ x ≤ 1 / 6) :
    ∀ i j, 0 < xs i → 0 < ss j → 5 * x j ≤ x i := by sorry

end RandomLPIPM
