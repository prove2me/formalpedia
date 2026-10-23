-- Prove2me | Theorems.Thm_PoolOrNot_Moderate_theorem_1
-- name    : PoolOrNot.Moderate.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:42.346888+00:00
-- url     : https://prove2.me/theorems/35bce6c3-8118-487c-874f-4d7808868a25
-- title:
--   Theorem 1, p. 7 — existence, uniqueness, Lipschitz continuity and 𝕊_N-invariance of the fluid solution
-- statement:
--   Let $\mu, \theta, \rho > 0$, let $q, \bar q$ be as in (18), and assume condition (19): the initial state $x = \bar Q(0)$ lies in $\mathbb S_N$ for some $N > \bar q + 1$. Then:
--
--   1. there exists a fluid solution $(\bar Q, \bar U)$ of (11)–(16) with $\bar Q(0) = x$;
--   2. every such solution has $\bar Q_i$ and $\bar U_i$ Lipschitz continuous on $[0, \infty)$ for each $i \in \mathbb N$, and $\bar Q(t) \in \mathbb S_N$ for all $t \ge 0$;
--   3. any two such solutions coincide for $t \ge 0$.
--
--   The theorem makes the fluid model a well-defined deterministic dynamical system on $\mathbb S_N$, the object whose long-run behavior (Theorem 2) approximates the many-server system.
--
--   **Formalization Note** Uniqueness is asserted on $t \ge 0$, for $\bar Q_i$ with $i \ge 1$ and for all $\bar U_i$: values at $t < 0$ and $\bar Q_0$ are not part of a fluid solution. The positivity of $\mu, \theta, \rho$ is implicit on the page (they are rates). The readings of (14) and (16) are those of the definition `PoolOrNot.Moderate.Fluid`.
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research, Articles in Advance (2020), doi:10.1287/opre.2019.1976, p. 7 (PDF 8), Theorem 1

import Mathlib
import Definitions.Def_PoolOrNot_Moderate_Chain
import Definitions.Def_PoolOrNot_Moderate_Fluid

namespace PoolOrNot.Moderate

/-- **Theorem 1**, p. 7. Under condition (19) (`Q̄(0) = x ∈ 𝕊_N` with `N > q̄ + 1`) there is a fluid
solution with `Q̄(0) = x`; every such solution has Lipschitz `Q̄_i`, `Ū_i` on `[0, ∞)` and stays in
`𝕊_N`; and any two such solutions agree on `t ≥ 0` (indices `i ≥ 1` for `Q̄`, all indices for `Ū`).
Rates `μ, θ > 0` and `ρ > 0` are implicit on the page. -/
theorem theorem_1 (ρ μ θ : ℝ) (hρ : 0 < ρ) (hμ : 0 < μ) (hθ : 0 < θ) (N : ℕ)
    (hN : qBar ρ μ θ + 1 < N) (x : ℕ → ℝ) (hx : InSN N x) :
    (∃ Q U : ℕ → ℝ → ℝ, IsFluidSolution ρ μ θ Q U ∧ ∀ i : ℕ, 1 ≤ i → Q i 0 = x i) ∧
    (∀ Q U : ℕ → ℝ → ℝ, IsFluidSolution ρ μ θ Q U → (∀ i : ℕ, 1 ≤ i → Q i 0 = x i) →
      (∀ i : ℕ, 1 ≤ i → (∃ K : NNReal, LipschitzOnWith K (Q i) (Set.Ici 0)) ∧
        ∃ K : NNReal, LipschitzOnWith K (U i) (Set.Ici 0)) ∧
      ∀ t : ℝ, 0 ≤ t → InSN N (fun i => Q i t)) ∧
    (∀ Q U Q' U' : ℕ → ℝ → ℝ, IsFluidSolution ρ μ θ Q U → IsFluidSolution ρ μ θ Q' U' →
      (∀ i : ℕ, 1 ≤ i → Q i 0 = x i) → (∀ i : ℕ, 1 ≤ i → Q' i 0 = x i) →
      (∀ i : ℕ, 1 ≤ i → ∀ t : ℝ, 0 ≤ t → Q i t = Q' i t) ∧
      ∀ i : ℕ, ∀ t : ℝ, 0 ≤ t → U i t = U' i t) := by sorry

end PoolOrNot.Moderate
