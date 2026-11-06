-- Prove2me | Theorems.Thm_QGChasing_theorem_1_1
-- name    : QGChasing.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:31:44.14697+00:00
-- url     : https://prove2.me/theorems/6821b2bb-e55b-41f6-b9d9-8cef9117a35b
-- title:
--   Theorem 1.1 — CPD is $\frac{32}{7}(1+\kappa^{1/3})$-competitive on $\mathcal F_\kappa$
-- statement:
--   In convex function chasing with Euclidean movement, a learner facing hitting costs $f_1,f_2,\dots$ chooses decisions $x_t\in X$ and pays $\sum_{t=1}^T\big(f_t(x_t)+\|x_t-x_{t-1}\|\big)$. The class $\mathcal F_\kappa$ consists of nonnegative convex costs that are $L_t$-smooth and have $\lambda_t$-quadratic growth on $\mathbb R^d$ around their global minimizer, with $L_t\le\kappa\lambda_t$; the parameters may change between rounds.
--
--   **Theorem.** For every $\kappa\ge1$, Clipped Proximal Descent (Algorithm 1) achieves the competitive ratio $C=\frac{32}{7}(1+\kappa^{1/3})$ on $\mathcal F_\kappa$. Precisely: for every dimension $d$, every nonempty closed convex $X\subseteq\mathbb R^d$, every initial decision $x_0\in X$ and every sequence $f_1,f_2,\ldots\in\mathcal F_\kappa$, the CPD trajectory $x_0,x_1,\dots$ satisfies, for every horizon $T$ and every comparator sequence $u_1,\dots,u_T\in X$ with $u_0=x_0$,
--   $$
--   \sum_{t=1}^T\big(f_t(x_t)+\|x_t-x_{t-1}\|\big)\ \le\ \frac{32}{7}\big(1+\kappa^{1/3}\big)\sum_{t=1}^T\big(f_t(u_t)+\|u_t-u_{t-1}\|\big).
--   $$
--
--   The ratio is dimension-free and of order $\kappa^{1/3}$. This improves the earlier $O(\sqrt\kappa)$ upper bound for well-conditioned costs and matches the known $\Omega(\kappa^{1/3})$ lower bound, while assuming quadratic growth in place of strong convexity.
--
--   **Formalization Note** Nonemptiness of $X$ follows from $x_0\in X$. The trajectory exists and is unique (milestone "Algorithm 1 is well defined"), so the hypothesis that $x$ is a CPD run is satisfiable.
--
--   Differences from the source:
--   - encoding: CR = Σ(f_t(x_t) + ‖x_t − x_{t−1}‖) / min_{u_1..u_T ∈ X} Σ(f_t(u_t) + ‖u_t − u_{t−1}‖) ≤ C → chasingCost f x T ≤ cpdC κ * chasingCost f u T for every u with u 0 = x 0 and u t ∈ X; reason: the ratio of nonnegative costs is at most C exactly when the bound holds against every feasible comparator; avoids a quotient with denominator 0
--   - encoding: CPD's decisions x_1, …, x_T (Algorithm 1 with its oracles) → a hypothesis IsCPDRun κ X f x (relational steps); reason: the run exists and is unique (cpd_step_exists_unique); sanity checks exhibit runs in both branches
--   - encoding: rounds t = 1, …, T; f_t ∈ F_κ with per-round λ_t, L_t → t + 1 for t ∈ Finset.range T; InFkappa κ (f t) for t ≥ 1 with the parameters existential inside; f 0 unused; reason: index shift; same instances
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Theorem 1.1, p.2 (with the definition of CR, p.1, F_κ, p.2, Assumptions 1–3 and 5, p.4, Algorithm 1, p.5, and (3), p.6)

import Mathlib
import Definitions.Def_QGChasing_InFkappa
import Definitions.Def_QGChasing_cpdC
import Definitions.Def_QGChasing_IsCPDRun
import Definitions.Def_QGChasing_chasingCost

namespace QGChasing

/-- **Theorem 1.1** (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.2). For any `κ ≥ 1`, CPD achieves a competitive ratio of
`(32/7)(1 + κ^{1/3})` on `F_κ`: for every dimension `d`, every nonempty closed convex decision set
`X ⊆ ℝᵈ` (Assumption 1), every initial decision `x₀ ∈ X` and every sequence of hitting costs
`f₁, f₂, … ∈ F_κ`, the CPD trajectory `x` satisfies, for every horizon `T` and every comparator
sequence `u₁, …, u_T ∈ X` with `u₀ = x₀`,
`∑_{t=1}^T (f_t(x_t) + ‖x_t − x_{t−1}‖) ≤ (32/7)(1 + κ^{1/3}) ∑_{t=1}^T (f_t(u_t) + ‖u_t − u_{t−1}‖)`.

**Formalization Note** The competitive ratio `CR = ALG / min_{u ∈ X^T} cost(u)` (p.1) is at most
`C` exactly when `ALG ≤ C · cost(u)` for every feasible comparator `u`; the theorem states the
latter, which avoids a quotient with denominator `0`. The trajectory is the hypothesis
`IsCPDRun` (it exists and is unique by `cpd_step_exists_unique`). Nonemptiness of `X` follows from
`x₀ ∈ X`. -/
theorem theorem_1_1 {d : ℕ} (κ : ℝ) (hκ : 1 ≤ κ) (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : IsClosed X)
    (hXcv : Convex ℝ X) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ t, 1 ≤ t → InFkappa κ (f t))
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (hx : IsCPDRun κ X f x) (T : ℕ) (u : ℕ → EuclideanSpace ℝ (Fin d)) (hu0 : u 0 = x 0)
    (huX : ∀ t, u t ∈ X) :
    chasingCost f x T ≤ cpdC κ * chasingCost f u T := by sorry

end QGChasing
