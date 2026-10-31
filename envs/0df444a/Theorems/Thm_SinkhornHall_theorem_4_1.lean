-- Prove2me | Theorems.Thm_SinkhornHall_theorem_4_1
-- name    : SinkhornHall.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:44.567983+00:00
-- url     : https://prove2.me/theorems/0f434966-cc9d-4ed7-8c21-8ad0570c9ec4
-- title:
--   Theorem 4.1 — without a perfect matching, after $\ell\ge\frac14 n^2\log(mA_{\max}/A_{\min})$ Sinkhorn iterations every step-2 output is a Hall blocker
-- statement:
--   Let $A$ be a nonnegative $n\times n$ real matrix with no zero row or column, and let $G=G(A)$ be its support graph (row $i$ and column $j$ adjacent iff $A_{ij}>0$). Let $m$ be the number of nonzero entries of $A$, $A_{\max}$ its largest entry and $A_{\min}$ its least positive entry. Run the algorithm *Sinkhorn & Sorting Scaling Vectors* with $(r,c)=(\mathbf 1,\mathbf 1)$:
--
--   1. **Step 0.** $x=y:=\mathbf 1$, then $y\leftarrow C(x)$, where $C(x)_j=1/\sum_iA_{ij}x_i$.
--   2. **Step 1.** Repeat $\ell$ times: $x\leftarrow R(y)$, $y\leftarrow C(x)$, where $R(y)_i=1/\sum_jA_{ij}y_j$.
--   3. **Step 2.** Sort $x_{i_1}\ge\dots\ge x_{i_n}$ and $y_{j_1}\le\dots\le y_{j_n}$, choose $k^*$ with $(x_{i_{k^*}}y_{j_{k^*}})^n\ge x_1\cdots x_ny_1\cdots y_n$, and output $X=\{i_1,\dots,i_{k^*}\}$.
--
--   **Theorem.** Suppose $G$ has no perfect matching and
--
--   $$\ell\ \ge\ \frac14\,n^2\log\frac{mA_{\max}}{A_{\min}} .$$
--
--   Then step 2 has an output, and every output $X$ of step 2 (for every tie-break in the two sorts and every admissible $k^*$) is a **Hall blocker**: $|\Gamma(X)|<|X|$, where $\Gamma(X)$ is the set of columns adjacent to $X$.
--
--   A Hall blocker certifies, by Hall's theorem, that $G$ has no perfect matching. The theorem shows that $O(n^2\log(mA_{\max}/A_{\min}))$ Sinkhorn iterations not only detect the absence of a perfect matching but also produce such a certificate by sorting the scaling vectors.
--
--   **Formalization Note** The scaling vectors after $\ell$ iterations are `sinkhorn A ℓ` ($\ell=0$ is the state right after step 0); step 2 is the relation `IsStep2Output`; $m$ is `numEdges A`; $\log$ is the natural logarithm and the threshold is a real inequality.
--
--   Differences from the source:
--   - reading: step 2 leaves the sort tie-breaks and the choice of k* open; 'the output is a Hall blocker' → every X with IsStep2Output (sinkhorn A ℓ) X is a Hall blocker; reason: the proof works for every admissible choice; this is the stronger reading
--   - generalization: 'the output is a Hall blocker' (existence of an output presupposed) → adds the conjunct ∃ X, IsStep2Output (sinkhorn A ℓ) X; reason: the paper presupposes step 2 is well posed; the Lean statement implies the source's claim and rules out a vacuous reading
--   - reading: log (base not named) → Real.log (natural logarithm); reason: the constants 1/2 (Pinsker), 4/n² and 1/4 are derived in the natural log
--   - reading: §4 standing assumptions (p.15): G = G(A) for a nonnegative n × n matrix A, no isolated node, n = |U| = |V|, (r, c) = (1, 1) → A : Matrix (Fin n) (Fin n) ℝ with hA, hrow, hcol, and marginals 1; reason: stated once at the top of §4 and in force for Theorem 4.1 and its proof
--   - encoding: m, the number of nonzero elements of A → numEdges A; reason: §2 uses m for the column count
--   - encoding: 'G has no perfect matching' → ¬ ∃ permutation σ with A i (σ i) > 0 for all i; reason: |U| = |V| = n, so a perfect matching is a bijection along edges
--   - encoding: 1-based indices i_1, …, i_n and k* ∈ {1, …, n} → Fin n (0-based), i_t = σ (t − 1), k = k* − 1, output σ '' {0, …, k}; reason: Lean convention; the output has k* elements as in the paper
--   - encoding: the vectors after ℓ iterations of step 1 → sinkhorn A ℓ, ℓ = 0 being the state after step 0; reason: Lean convention for the algorithm's state
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Theorem 4.1, p.15 (algorithm: §4.1, Algorithm: Sinkhorn & Sorting Scaling Vectors, p.15; setting: §4, p.15; proof pp.15–16)

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall

/-- **Theorem 4.1.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Theorem 4.1, p.15: "Suppose that G has no perfect
matching. For ℓ ≥ (1/4)n² log mA_max/A_min, the output is a Hall blocker."

The algorithm is "Sinkhorn & Sorting Scaling Vectors" (§4.1, p.15): step 0 sets `x = y := 1` and
`y ← C(x)`; step 1 repeats `x ← R(y)`, `y ← C(x)` `ℓ` times; step 2 sorts `x` decreasingly and `y`
increasingly, chooses `k*` with `(x_{i_{k*}} y_{j_{k*}})ⁿ ≥ x₁⋯xₙy₁⋯yₙ` and outputs
`{i₁, …, i_{k*}}`. Setting of §4 (p.15): `G = G(A)` for a nonnegative `n × n` matrix `A` with no
isolated node (no zero row or column), `(r, c) = (1, 1)`; `m` is the number of nonzero entries of
`A`, `A_max` its largest entry and `A_min` its least positive entry.

Conclusion: an output of step 2 exists, and every output of step 2 (every tie-break of the sorts,
every admissible `k*`) is a Hall blocker, `|Γ(X)| < |X|`.

**Formalization Note.** `(x, y) = sinkhorn A ℓ`; `ℓ = 0` is the state right after step 0. Indices
are `Fin n` (0-based). `log` is `Real.log`, and the threshold is the real inequality
`(1/4) n² log(m A_max / A_min) ≤ ℓ` with `m = numEdges A`. -/
theorem theorem_4_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j)
    (hpm : ¬ HasPerfectMatching A) (ℓ : ℕ)
    (hℓ : (1 / 4 : ℝ) * (n : ℝ) ^ 2 * Real.log ((numEdges A : ℝ) * Amax A / Amin A) ≤ ℓ) :
    (∃ X, IsStep2Output (sinkhorn A ℓ).1 (sinkhorn A ℓ).2 X) ∧
      ∀ X, IsStep2Output (sinkhorn A ℓ).1 (sinkhorn A ℓ).2 X → IsHallBlocker A X := by sorry

end SinkhornHall
