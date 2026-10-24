-- Prove2me | Theorems.Thm_PermInvConvex_Sparsity_theorem_3_2
-- name    : PermInvConvex.Sparsity.theorem_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:03.605407+00:00
-- url     : https://prove2.me/theorems/c91f4bd1-2ccc-4613-8659-4ae9d533b6a2
-- title:
--   Theorem 3.2 (Sparsity Theorem), p. 9 — u(x) of (15) minimizes ‖u‖s over sparse sorted weak majorants of |x|; with p. 6, opt ≤ 1 iff x ∈ conv(N^K)
-- statement:
--   Let $\|\cdot\|_s$ be a symmetric gauge function (sign- and permutation-invariant norm) on $\mathbb R^n$, let $K$ be an integer with $1 < K < n$, and let $x \in \mathbb R^n$. Consider
--
--   $$\begin{aligned} \min\ & \|u\|_s \\ \text{s.t.}\ & u_1 \ge \dots \ge u_K \ge 0, \\ & u_{K+1} = \dots = u_n = 0, \\ & u \ge_{wm} |x|. \end{aligned} \tag{11}$$
--
--   Then:
--
--   1. **(Sparsity Theorem)** the closed-form vector $u(x)$ of (15) is an optimal solution of (11): it is feasible, and $\|u(x)\|_s \le \|u\|_s$ for every feasible $u$;
--   2. the optimal value of (11) is at most $1$ if and only if $x \in \operatorname{conv}(N^K_{\|\cdot\|_s})$, where $N^K_{\|\cdot\|_s} = \{x \mid \|x\|_s \le 1,\ \operatorname{card}(x) \le K\}$:
--   $$x \in \operatorname{conv}\big(N^K_{\|\cdot\|_s}\big) \iff \|u(x)\|_s \le 1.$$
--
--   The theorem gives a membership test and a closed-form optimal solution for the convex hull of a cardinality-constrained norm ball, the feasible set of sparse principal component analysis when $\|\cdot\|_s$ is the Euclidean norm.
--
--   **Formalization Note** Part 1 is Theorem 3.2 as printed on p. 9. Part 2 is the reading of the theorem given on p. 6 ("the optimal value of (11) is no more than 1 if and only if $x \in \operatorname{conv}(N^K)$"); by Part 1 the optimal value equals $\|u(x)\|_s$, which is how it is written. $1 < K < n$ is the standing assumption of §3 (p. 6). Lean vector index $i$ is the paper's $i+1$; $u_K \ge 0$ is stated as $u_i \ge 0$ for all $i \le K$ (equivalent given the chain). $\|\cdot\|_s$ is an arbitrary function satisfying the symmetric-gauge axioms, not Lean's sup norm.
-- source:
--   Kim, Tawarmalani, Richard, Convexification of Permutation-Invariant Sets and an Application to Sparse PCA, arXiv:1910.02573v2, p. 9, Theorem 3.2 (Sparsity Theorem), with p. 6, (11) and the sentence introducing it; standing assumption 1 < K < n, p. 6

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting

namespace PermInvConvex.Sparsity

theorem theorem_3_2 {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (hK : 1 < K) (hKn : K < n) (x : Fin n → ℝ) :
    (uVec K x ∈ Feas11 K x ∧ ∀ u ∈ Feas11 K x, ns (uVec K x) ≤ ns u) ∧
    (x ∈ convexHull ℝ (NK ns K) ↔ ns (uVec K x) ≤ 1) := by sorry

end PermInvConvex.Sparsity
