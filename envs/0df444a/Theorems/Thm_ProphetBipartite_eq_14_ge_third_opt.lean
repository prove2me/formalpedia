-- Prove2me | Theorems.Thm_ProphetBipartite_eq_14_ge_third_opt
-- name    : ProphetBipartite.eq_14_ge_third_opt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:50:10.369565+00:00
-- url     : https://prove2.me/theorems/7baa025c-7478-4f67-a734-a5d784eadfed
-- title:
--   Proof of Theorem 3.1 — at a solution of (16), expression (14) is at least $\frac13\,\mathbb 1_L^\top M\mathbb 1_R$
-- statement:
--   Let $M$, $Q$ be real $L\times R$ matrices with nonnegative entries such that every row sum and every column sum of $Q$ is at most $1$ (Fact 3.2), and let $l\in\mathbb R^L$, $r\in\mathbb R^R$ solve the system (16), equivalently (17):
--
--   $$
--   l_i=\sum_{j}\big[M_{i,j}-Q_{i,j}(l_i+r_j)\big]^+,\qquad r_j=\sum_{i}\big[M_{i,j}-Q_{i,j}(l_i+r_j)\big]^+ .
--   $$
--
--   Then $l\ge0$, $r\ge0$, and for all $S_L\subseteq L$, $S_R\subseteq R$,
--
--   $$
--   3\Big(\sum_{i\in S_L}l_i+\sum_{j\in S_R}r_j+\sum_{i\notin S_L}\sum_{j\notin S_R}\big[M_{i,j}-(l_i+r_j)Q_{i,j}\big]^+\Big)\ \ge\ \sum_{i\in L}\sum_{j\in R}M_{i,j}.
--   $$
--
--   The bracket is the objective of (14) at $\alpha=\mathbb 1_{S_L}$, $\beta=\mathbb 1_{S_R}$, so the minimum (14) is at least one third of $\mathbb 1_L^\top M\mathbb 1_R$, the prophet's value by (12). Combined with (11), this is the 3-approximation of Theorem 3.1.
--
--   Differences from the source:
--   - generalization: M, Q are the matrices of (10) → any real L × R matrices with nonnegative entries whose Q has row sums and column sums at most 1; reason: the proof uses only these properties of M, Q (Fact 3.2 and nonnegativity); the matrices of (10) are an instance by fact_3_2
--   - encoding: (14) ≥ opt/3, with (14) the minimum over α ∈ {0,1}ⁿ, β ∈ {0,1}ᵐ → 3 · (objective at (S_L, S_R)) ≥ ∑ M for every pair of finsets; reason: a minimum over a finite set is ≥ c iff every value is; multiplying by 3 avoids division
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, proof of Theorem 3.1, (14)–(16) and the closing display, p.9

import Mathlib
import Definitions.Def_ProphetBipartite_IsSolution17

namespace ProphetBipartite

/-- **Proof of Theorem 3.1, (14)–(16) and the closing display: at a solution of (16), expression (14)
is at least one third of `𝟙_Lᵀ M 𝟙_R`.** Gravin & Wang, arXiv:1902.06243v1, p.9: "We will find non
negative price vectors `l, r`, s.t. (14) `≥ opt/3`" and "Finally, we show that expression (14) is
at least `opt/3` of the prophet's expected value."

Let `M`, `Q` be real `L × R` matrices with nonnegative entries whose row sums and column sums of `Q`
are at most 1 (Fact 3.2), and let `l, r` solve (16)/(17). Then `l, r ≥ 0`, and for every
`S_L ⊆ L`, `S_R ⊆ R`,

`3 · ( ∑_{i∈S_L} l_i + ∑_{j∈S_R} r_j + ∑_{i∉S_L, j∉S_R} [M_{i,j} − (l_i + r_j)·Q_{i,j}]⁺ ) ≥ ∑_{i,j} M_{i,j}`.

The left-hand bracket is the objective of (14) at `α = 𝟙_{S_L}`, `β = 𝟙_{S_R}`, so the minimum (14)
is at least `𝟙_Lᵀ M 𝟙_R / 3`.

**Formalization Note.** The statement is about arbitrary matrices with the properties the paper uses
of its `M`, `Q` (nonnegativity and Fact 3.2); the matrices of (10) are an instance. -/
theorem eq_14_ge_third_opt {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (M Q : L → R → ℝ) (hM : ∀ i j, 0 ≤ M i j) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j ≤ 1) (hcol : ∀ j, ∑ i, Q i j ≤ 1)
    (l : L → ℝ) (r : R → ℝ) (hlr : IsSolution17 M Q l r) :
    (∀ i, 0 ≤ l i) ∧ (∀ j, 0 ≤ r j) ∧
      ∀ (SL : Finset L) (SR : Finset R),
        ∑ i, ∑ j, M i j ≤
          3 * (∑ i ∈ SL, l i + ∑ j ∈ SR, r j +
            ∑ i ∈ SLᶜ, ∑ j ∈ SRᶜ, max (M i j - (l i + r j) * Q i j) 0) := by sorry

end ProphetBipartite
