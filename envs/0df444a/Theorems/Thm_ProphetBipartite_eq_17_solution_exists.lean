-- Prove2me | Theorems.Thm_ProphetBipartite_eq_17_solution_exists
-- name    : ProphetBipartite.eq_17_solution_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:50:13.851426+00:00
-- url     : https://prove2.me/theorems/74177751-f1cf-42ae-8f1c-763c589fa6e6
-- title:
--   End of the proof of Theorem 3.2 — the iterates of Algorithm 1 converge to an exact solution of (17)
-- statement:
--   Let $M$, $Q$ be real $L\times R$ matrices with nonnegative entries such that every row sum and every column sum of $Q$ is at most $1$, and let $l^{(0)}\in\mathbb R^L$, $r^{(0)}\in\mathbb R^R$ be any initial vectors. Then the iterates $(l(t),r(t))$ of Algorithm 1 started from them, run without the stopping test, converge as $t\to\infty$ to vectors $l\in\mathbb R^L$, $r\in\mathbb R^R$ with
--
--   $$
--   l_i=\sum_{j\in R}\big[M_{i,j}-Q_{i,j}(l_i+r_j)\big]^+\ \ \forall i\in L,\qquad
--   r_j=\sum_{i\in L}\big[M_{i,j}-Q_{i,j}(l_i+r_j)\big]^+\ \ \forall j\in R .
--   $$
--
--   In particular (17), equivalently (16), has an exact solution, which is what the proof of Theorem 3.1 assumes and §3.3 establishes.
--
--   Differences from the source:
--   - generalization: M, Q are the matrices of (10) → any real L × R matrices with nonnegative entries whose Q has row sums and column sums at most 1; reason: the proof uses only these properties of M, Q (Fact 3.2 and nonnegativity); the matrices of (10) are an instance by fact_3_2
--   - encoding: Algorithm 1 with the stopping test of line 9 → the iterates (algorithm1Step M Q)^[t] of one round, without a stopping test; reason: the proof of Theorem 3.2 itself lets the algorithm "continue indefinitely" (p.11); the stopping test changes no iterate before it fires
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, end of the proof of Theorem 3.2, pp.11–12; system (17), p.10; deferred from p.9

import Mathlib
import Definitions.Def_ProphetBipartite_IsSolution17
import Definitions.Def_ProphetBipartite_algorithm1Step

open Filter Topology

namespace ProphetBipartite

/-- **Algorithm 1 converges to an exact solution of (17).** Gravin & Wang, arXiv:1902.06243v1,
end of the proof of Theorem 3.2, pp.11–12: "if we let the Algorithm 1 to continue indefinitely, it
will produce a sequence of states `s_t = (l(t), r(t)) ∈ ℝ^{n+m}` for each iteration `t` that converges
to an exact solution of (17)"; the limit "`s ∈ ℝ^{n+m}` … must be an exact solution to (17)". In
particular (17) has a solution, the existence of a solution of (16) assumed in the proof of Theorem
3.1 (p.9, "We give an algorithmic proof for the existence of the solution to (16) in the next
section").

For real `L × R` matrices `M`, `Q` with nonnegative entries whose row sums and column sums of `Q` are
at most 1, and any initial vectors `l₀`, `r₀`, the iterates of Algorithm 1 converge to real vectors
`l`, `r` with
`l_i = ∑_j [M_{i,j} − Q_{i,j}(l_i + r_j)]⁺` for every `i` and
`r_j = ∑_i [M_{i,j} − Q_{i,j}(l_i + r_j)]⁺` for every `j`.

**Formalization Note.** The bounds on the sums of `Q` are Fact 3.2, which the proof of Theorem 3.2
uses (p.11); Algorithm 1's input is "matrices of non negative real numbers" and its initialization
"can be arbitrary" (p.10). The iterates are `(algorithm1Step M Q)^[t] (l₀, r₀)`, the algorithm
without its stopping rule; the limit is in the product topology of `(L → ℝ) × (R → ℝ)`, which is the
`L₁` topology of `ℝ^{n+m}`. -/
theorem eq_17_solution_exists {L R : Type*} [Fintype L] [Fintype R]
    (M Q : L → R → ℝ) (hM : ∀ i j, 0 ≤ M i j) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j ≤ 1) (hcol : ∀ j, ∑ i, Q i j ≤ 1) (l₀ : L → ℝ) (r₀ : R → ℝ) :
    ∃ (l : L → ℝ) (r : R → ℝ),
      Tendsto (fun t : ℕ => (algorithm1Step M Q)^[t] (l₀, r₀)) atTop (𝓝 (l, r)) ∧
        IsSolution17 M Q l r := by sorry

end ProphetBipartite
