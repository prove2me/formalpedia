-- Prove2me | Theorems.Thm_WassTwoStage_Copositive_theorem_5
-- name    : WassTwoStage.Copositive.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:58:29.558994+00:00
-- url     : https://prove2.me/theorems/abdf0e92-4667-497d-88d7-67a843e9cb16
-- title:
--   Theorem 5 — the copositive programs (28): exact under complete recourse, bounds on (1), and convergence as δ ↓ 0
-- statement:
--   Assume the setting of §3: the support $\Xi = \{\xi\ge0 : S\xi\le t\}$ is non-empty, the problem has sufficiently expensive recourse, $I\ge1$, every sample $\hat\xi_i$ lies in $\Xi$, and $\epsilon\ge0$. Let $c\in\mathbb R^{N_1}$ and $\mathcal X\subseteq\mathbb R^{N_1}$. Consider problem (1),
--   $$\text{minimize}\ c^\top x + \mathcal Z(x)\quad\text{subject to}\ x\in\mathcal X,$$
--   and the family of copositive programs (28), parametrized by $\delta\ge0$,
--   $$\text{minimize}\ c^\top x + \epsilon^2\lambda + \frac1I\sum_{i\in[I]}\Big[s_i + \boldsymbol q^\top\psi_i - \lambda\|\hat\xi_i\|_2^2 + \sum_{j\in[N_2+J]}\phi_{ij}\boldsymbol q_j^2\Big]$$
--   over $x\in\mathcal X$, $\lambda\in\mathbb R_+$, $s_i\in\mathbb R$, $\psi_i,\phi_i\in\mathbb R^{N_2+J}$, subject to the copositivity of the block matrices of (24) for every $i\in[I]$. Then:
--   1. if $\delta = 0$ and (1) has complete recourse, (28) is equivalent to (1): the two optimal values coincide, and $x$ is a minimizer for (28) if and only if it is a minimizer for (1);
--   2. if $\delta = 0$, the optimal value of (28) is an upper bound on that of (1);
--   3. if $\delta > 0$, the optimal value of (28) is a lower bound on that of (1);
--   4. if $\mathcal X$ is compact, the optimal value of (28) converges to that of (1) as $\delta\downarrow0$; moreover, if $\delta_n\downarrow0$ and each $x_n$ is a minimizer for (28) at $\delta_n$, then every cluster point $x^\star$ of $(x_n)$ is a minimizer for (1).
--
--   This is the paper's main theorem: (1) is equivalent to a copositive program under complete recourse, and in general it is sandwiched between, and approximated arbitrarily well by, copositive programs.
--
--   **Formalization Note** Optimal values are infima in `EReal`, and the limit in item 4 is in the order topology of $[-\infty,+\infty]$, from the right. A minimizer for (28) at $\delta$ is a point $x\in\mathcal X$ minimizing $c^\top x + \overline{\mathcal Z}_\delta(x)$ (the first-stage part of a solution, as in the paper's proof); the inner infimum over $(\lambda,s,\psi,\phi)$ need not be attained. The paper's item (ii) assumes that (1) fails to have complete recourse; that assumption is not used by the bound and is dropped, giving a slightly stronger statement. "A sequence $\{x^\star_\delta\}_{\delta\downarrow0}$" is read as a sequence $x_n$ indexed along any sequence $\delta_n > 0$ with $\delta_n \to 0$. The hypotheses $I\ge1$ and $\hat\xi_i\in\Xi$ are implicit in the paper.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, pp. 18–19, Theorem 5, (28); proof p. 19

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_ConicPrograms

open Filter Topology

namespace WassTwoStage.Copositive

/-- Theorem 5, Hanasusanto–Kuhn, arXiv:1609.07505v3, pp. 18–19: the family (28) of copositive
programs, parametrized by `δ ≥ 0`, versus problem (1), under the standing assumptions of §3.
(i) for `δ = 0` and complete recourse, (28) is equivalent to (1): same optimal value and same
minimizers; (ii) for `δ = 0`, (28) is an upper bound on (1); (iii) for `δ > 0`, (28) is a
lower bound on (1); (iv) if `𝒳` is compact, the optimal value of (28) converges to that of (1)
as `δ ↓ 0`, and every cluster point of a sequence of minimizers of (28) along `δ_n ↓ 0` is a
minimizer of (1). -/
theorem theorem_5 {K J M N₁ N₂ I : ℕ} (d : Data K J M N₁ N₂ I) (c : Fin N₁ → ℝ)
    (X : Set (Fin N₁ → ℝ)) (hI : 0 < I) (hXi : d.Xi.Nonempty)
    (hSER : d.SufficientlyExpensiveRecourse) (hξ : ∀ i, d.ξhat i ∈ d.Xi) (hε : 0 ≤ d.ε) :
    (d.CompleteRecourse →
      d.val28 c X 0 = d.val1 c X ∧
      ∀ x, d.IsMinimizer28 c X 0 x ↔ d.IsMinimizer1 c X x) ∧
    d.val1 c X ≤ d.val28 c X 0 ∧
    (∀ δ : ℝ, 0 < δ → d.val28 c X δ ≤ d.val1 c X) ∧
    (IsCompact X →
      Tendsto (fun δ => d.val28 c X δ) (𝓝[>] 0) (𝓝 (d.val1 c X)) ∧
      ∀ (δs : ℕ → ℝ) (xs : ℕ → Fin N₁ → ℝ),
        Tendsto δs atTop (𝓝[>] 0) →
        (∀ n, d.IsMinimizer28 c X (δs n) (xs n)) →
        ∀ xstar : Fin N₁ → ℝ, MapClusterPt xstar atTop xs → d.IsMinimizer1 c X xstar) := by sorry

end WassTwoStage.Copositive
