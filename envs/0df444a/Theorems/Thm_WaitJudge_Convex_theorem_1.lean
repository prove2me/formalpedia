-- Prove2me | Theorems.Thm_WaitJudge_Convex_theorem_1
-- name    : WaitJudge.Convex.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:07:35.11104+00:00
-- url     : https://prove2.me/theorems/82151b4f-bd3f-486c-bf1b-db76bedaac20
-- title:
--   Theorem 1, p. 10 — ℙᴺ{V(x*_N) > ε(s*_N)} ≤ γ* with γ* the value of (10)
-- statement:
--   Let $x\in\mathbb R^d$ be the optimization variable, $c\in\mathbb R^d$ a cost vector, $\mathcal X\subseteq\mathbb R^d$ a convex domain, and $\mathcal X_\delta\subseteq\mathbb R^d$ convex constraint sets indexed by $\delta$ in a probability space $(\Delta,\mathcal F,\mathbb P)$. Ties are broken by minimising convex functions $t_1,\dots,t_p$ in succession. Let $\delta^{(1)},\dots,\delta^{(N)}$ be an i.i.d. sample with $N>d$, let $x^*_N$ be the solution of the scenario program
--   $$\min_{x\in\mathcal X}c^{\mathsf T}x\quad\text{subject to } x\in\bigcap_{i=1}^N\mathcal X_{\delta^{(i)}},$$
--   let $s^*_N$ be its number of support constraints, and let $V(x)=\mathbb P\{\delta: x\notin\mathcal X_\delta\}$ be the violation.
--
--   Let $\epsilon(k)$, $k=0,1,\dots,d$, be any $[0,1]$-valued function. Under Assumptions 1 and 2,
--   $$\mathbb P^N\{V(x^*_N)>\epsilon(s^*_N)\}\ \le\ \gamma^*,$$
--   where $\gamma^*$ is the value of the variational problem (10):
--   $$\gamma^*=\inf_{\xi\in C^d[0,1]}\xi(1)\quad\text{subject to}\quad\frac1{k!}\frac{\mathrm d^k}{\mathrm dt^k}\xi(t)\ge\binom Nk t^{N-k}\,\mathbf 1_{[0,1-\epsilon(k))}(t),\ \ t\in[0,1],\ k=0,1,\dots,d.$$
--
--   The theorem lets the user observe the number of support constraints after solving and then certify the solution at the level $\epsilon(s^*_N)$, with a confidence that holds uniformly over all convex problems and all distributions.
--
--   **Formalization Note** Assumption 1 is required for every sample (as on the page), Assumption 2 almost surely. The measurability the paper takes for granted (footnote 1) is assumed as two hypotheses: the set $\{(x,\delta):x\in\mathcal X_\delta\}$ is measurable and every solution map $\omega\mapsto x^*_m(\omega)$ is Borel measurable. $N>d$ is the paper's standing assumption (p. 2). The probability is compared with $\gamma^*$ through $\mathrm{ofReal}$; $\gamma^*\in[0,1]$.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF p. 10, Theorem 1 and (10); setting PDF pp. 2–4, 8–9

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting

open MeasureTheory ScenarioApproach.Generalization

namespace WaitJudge.Convex

theorem theorem_1 {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]
    (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ)
    (hX : Convex ℝ X) (hXδ : ∀ δ, Convex ℝ (Xδ δ))
    (htb : ∀ j, ConvexOn ℝ Set.univ (tb j))
    (hA1 : Assumption1 c X Xδ tb) (hA2 : Assumption2 c X Xδ tb P)
    (hmeas : MeasurabilityPins c X Xδ tb)
    (N : ℕ) (hN : d < N) (ε : ℕ → ℝ) (hε : ∀ k ≤ d, 0 ≤ ε k ∧ ε k ≤ 1) :
    (Measure.pi fun _ : Fin N => P) {ω | ε (sstar c X Xδ tb ω) < violation P Xδ (xstar c X Xδ tb ω)} ≤ ENNReal.ofReal (gammaStar N d ε) := by sorry

end WaitJudge.Convex
