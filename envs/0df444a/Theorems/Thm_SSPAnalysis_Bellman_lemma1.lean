-- Prove2me | Theorems.Thm_SSPAnalysis_Bellman_lemma1
-- name    : SSPAnalysis.Bellman.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:10:40.483489+00:00
-- url     : https://prove2.me/theorems/ce8e9215-7cbd-454f-b39e-9236c76fc01a
-- title:
--   Lemma 1 — proper-policy fixed points and the super-solution test
-- statement:
--   Under Assumption 1, a proper stationary selector $\mu$ has a finite cost vector $x(\mu)$ in $X$. It is the unique fixed point of $T_\mu$ within $X$, and iteration of $T_\mu$ from every $x\in X$ converges to it. Conversely, if a vector $x\in X$ satisfies $x\ge T_\mu(x)$ componentwise, then $\mu$ is proper:
--
--   $$\mu\text{ proper}\Longrightarrow T_\mu(x(\mu))=x(\mu),\quad T_\mu^t(x)\to x(\mu);\qquad x\ge T_\mu(x)\Longrightarrow\mu\text{ proper}.$$
--
--   The two parts are one numbered lemma in the paper. They support both policy improvement and the fixed-point characterization of optimality.
--
--   **Formalization Note.** The finite real vector representing $x(\mu)$ is a conclusion, with equality to the extended-real cost proved coordinatewise. State $1$ is `0 : Fin n`. No compactness or Assumption 2 is required.
-- source:
--   Bertsekas and Tsitsiklis, An Analysis of Stochastic Shortest Path Problems, Math. Oper. Res. 16(3) (1991), p. 586, Lemma 1(a)–(b)

import Mathlib
import Definitions.Def_SSPAnalysis_Bellman_SSP

namespace SSPAnalysis.Bellman

open Filter Topology

/-- Lemma 1 (p. 586), both parts: proper policies have unique fixed-point
costs and attracting iterates; a super-solution forces properness. -/
theorem lemma1 {n : ℕ} [NeZero n] {U : Fin n → Type*}
    (m : Model n U) (h1 : m.Assumption1) :
    (∀ μ : Selector U, m.IsProper μ →
      ∃ xr : Fin n → ℝ,
        (∀ i, (xr i : EReal) = m.cost (stationary μ) i) ∧
        xr ∈ X n ∧ m.Tmu μ xr = xr ∧
        (∀ y ∈ X n, m.Tmu μ y = y → y = xr) ∧
        (∀ x ∈ X n,
          Tendsto (fun t : ℕ => (m.Tmu μ)^[t] x) atTop (𝓝 xr))) ∧
    (∀ μ : Selector U, ∀ x ∈ X n,
      (∀ i, m.Tmu μ x i ≤ x i) → m.IsProper μ) := by sorry

end SSPAnalysis.Bellman
