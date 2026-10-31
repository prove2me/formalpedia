-- Prove2me | Theorems.Thm_SAPMM_Regret_lemma_2_2
-- name    : SAPMM.Regret.lemma_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:24.6246+00:00
-- url     : https://prove2.me/theorems/a4558b64-07ca-4ff9-83bc-e7014bebd091
-- title:
--   Lemma 2.2, p. 5 — Σ_{t<T} G_i(x^t, ξ_t) ≤ λ_i^T/σ + Σ_{t<T} ‖v_i(x^t, ξ_t)‖‖x^{t+1} − x^t‖, (2.3)
-- statement:
--   Let $(x^t,\lambda^t)_{t\ge0}$ be a run of PMMSopt (1.5) with parameters $\sigma>0$, $\alpha>0$, started at $x^0\in X_0$ with $\lambda^0=0$, for a problem satisfying the standing assumptions of §1 and (A2)–(A4) (see the definition file). The run is driven by an arbitrary sample path $\xi_0,\xi_1,\dots$; no probabilistic assumption is needed. Let $v_i(x,\xi)$ be the oracle's stochastic subgradient of $G_i(\cdot,\xi)$.
--
--   Then for every horizon $T\ge0$ and every $i\in\{1,\dots,p\}$,
--
--   $$
--   \sum_{t=0}^{T-1}G_i(x^t,\xi_t)\le\frac1\sigma\lambda_i^T+\sum_{t=0}^{T-1}\|v_i(x^t,\xi_t)\|\,\|x^{t+1}-x^t\|.
--   $$
--
--   The cumulative constraint values along the run are bounded by the final multiplier plus a term controlled by the primal step lengths; this is the first half of the constraint-violation bound.
--
--   **Formalization Note** The statement is pathwise: it holds for every $\omega$, and (A1) is not assumed (more general than the page, whose proof does not use it). The hypothesis $x^0\in X_0$ corrects Step 0, which prints $x^0\in\mathbb R^n$; it is needed so that $x^0$ lies in $O_0$, where the subgradient and boundedness assumptions apply. Norms are Euclidean on $\mathbb R^n$ and $\mathbb R^p$.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, p. 5, Lemma 2.2, (2.3)

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- Lemma 2.2, p. 5, (2.3): the constraint sum is controlled by the last multiplier. -/
theorem lemma_2_2 {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Problem n p Ξ) (hP : P.Standing) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P σ α x0 ξ x lam) :
    ∀ (T : ℕ) (i : Fin p) ω,
      ∑ t ∈ Finset.range T, P.G (x t ω) (ξ t ω) i ≤
        1 / σ * lam T ω i
          + ∑ t ∈ Finset.range T, ‖P.v i (x t ω) (ξ t ω)‖ * ‖x (t + 1) ω - x t ω‖ := by sorry

end SAPMM.Regret
