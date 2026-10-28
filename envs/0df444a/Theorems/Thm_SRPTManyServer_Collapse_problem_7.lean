-- Prove2me | Theorems.Thm_SRPTManyServer_Collapse_problem_7
-- name    : SRPTManyServer.Collapse.problem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:36.352152+00:00
-- url     : https://prove2.me/theorems/d07ed470-ddc6-44d7-99db-ef0a2ecae1bb
-- title:
--   Problem (7), p. 18 — $\min \int x g\gamma$ s.t. $\int g\gamma \ge G(\tau)$, $\gamma \in [0,1]$, is $\mathbb E[S\mathbf 1\{S\le\tau\}]$, attained at $\gamma = \mathbf 1\{x\le\tau\}$
-- statement:
--   Let $g \ge 0$ be a measurable function such that $g$ and $x \mapsto x g(x)$ are integrable on $[0,\infty)$, and let $\tau \in \mathbb R$. Consider the optimization problem over measurable $\gamma$:
--   $$\min_\gamma \int_0^\infty x g(x)\gamma(x)\,dx \quad\text{s.t.}\quad \int_0^\infty g(x)\gamma(x)\,dx \ge \int_0^\tau g(x)\,dx,\qquad \gamma(x)\in[0,1]\ \text{for all } x \in [0,\infty).$$
--   Its minimum value is
--   $$\int_0^\tau x g(x)\,dx,$$
--   which is $\mathbb E[S\,\mathbf 1\{S \le \tau\}]$ when $g$ is the service-time density, and the minimum is attained at $\gamma(x) = \mathbf 1\{x \le \tau\}$.
--
--   This is the deterministic optimization step in the proof of Lemma 5. It says that, among service-probability profiles with at least the throughput $G(\tau)$, the least work is consumed by serving exactly the jobs shorter than $\tau$.
--
--   **Formalization Note** $\int_0^\tau$ is the integral over $[0,\tau]$; it vanishes for $\tau < 0$. The conclusion has three parts: $\int_0^\tau x g$ is the least value of the problem, $\mathbf 1\{x\le\tau\}$ is feasible, and it attains that value. Measurability of $\gamma$ is required, as the paper's integrals presuppose. The page writes "achieved when $\gamma(x) = 1\{x \le T\}$"; the $T$ is a typo for $\tau$.
-- source:
--   Dong & Ibrahim, On the SRPT scheduling discipline in many-server queues with impatient customers, arXiv:2102.05789v1, p. 18, proof of Lemma 5, problem (7)

import Mathlib

namespace SRPTManyServer.Collapse

open MeasureTheory

/-- **Problem (7)** (proof of Lemma 5, p. 18). Let `g ≥ 0` be measurable with `g` and `x ↦ x g(x)`
integrable on `[0, ∞)`. Over measurable `γ` with `γ(x) ∈ [0, 1]` for `x ≥ 0` and
`∫_0^∞ g γ ≥ ∫_0^τ g`, the least value of `∫_0^∞ x g(x) γ(x) dx` is `∫_0^τ x g(x) dx`, and it is
attained by `γ = 1{x ≤ τ}`. -/
theorem problem_7 (g : ℝ → ℝ) (hg_meas : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hg_int : IntegrableOn g (Set.Ici 0))
    (hxg_int : IntegrableOn (fun x => x * g x) (Set.Ici 0)) (tau : ℝ) :
    IsLeast
      {v : ℝ | ∃ γ : ℝ → ℝ, Measurable γ ∧ (∀ x, 0 ≤ x → γ x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∫ x in Set.Icc 0 tau, g x) ≤ (∫ x in Set.Ici 0, g x * γ x) ∧
        v = ∫ x in Set.Ici 0, x * g x * γ x}
      (∫ x in Set.Icc 0 tau, x * g x) ∧
    (∫ x in Set.Icc 0 tau, g x) ≤
        (∫ x in Set.Ici 0, g x * (Set.Iic tau).indicator (fun _ => (1 : ℝ)) x) ∧
    (∫ x in Set.Ici 0, x * g x * (Set.Iic tau).indicator (fun _ => (1 : ℝ)) x) =
        ∫ x in Set.Icc 0 tau, x * g x := by sorry

end SRPTManyServer.Collapse
