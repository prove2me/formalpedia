-- Prove2me | Theorems.Thm_SAPMM_Regret_lemma_2_3
-- name    : SAPMM.Regret.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:28.385117+00:00
-- url     : https://prove2.me/theorems/b674e394-20b0-4b48-828d-ceda75c33d87
-- title:
--   Lemma 2.3, p. 6 — three-point inequality (2.5) of the PMMSopt proximal step
-- statement:
--   Let $(x^t,\lambda^t)_{t\ge0}$ be a run of PMMSopt (1.5) with parameters $\sigma>0$, $\alpha>0$, started at $x^0\in X_0$ with $\lambda^0=0$, for a problem satisfying the standing assumptions of §1 and (A2)–(A4) (see the definition file). The run is driven by an arbitrary sample path $\xi_0,\xi_1,\dots$; no probabilistic assumption is needed.
--
--   Then for every $t\ge0$ and every $x\in X_0$,
--
--   $$
--   F(x^{t+1},\xi_t)+\frac1{2\sigma}\|\lambda^{t+1}\|^2+\frac\alpha2\|x^{t+1}-x^t\|^2\le F(x,\xi_t)+\frac1{2\sigma}\big\|[\lambda^t+\sigma G(x,\xi_t)]_+\big\|^2+\frac\alpha2\big[\|x-x^t\|^2-\|x-x^{t+1}\|^2\big].
--   $$
--
--   This is the basic inequality of the proximal step: it compares the new iterate with an arbitrary point of $X_0$ and is the starting point of the step-length bound, the drift lemma and the objective bound.
--
--   **Formalization Note** The statement is pathwise: it holds for every $\omega$, and (A1) is not assumed (more general than the page, whose proof does not use it). The hypothesis $x^0\in X_0$ corrects Step 0, which prints $x^0\in\mathbb R^n$; it is needed so that $x^0$ lies in $O_0$, where the subgradient and boundedness assumptions apply. Norms are Euclidean on $\mathbb R^n$ and $\mathbb R^p$.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, p. 6, Lemma 2.3, (2.5)

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- Lemma 2.3, p. 6, (2.5): the three-point inequality of the proximal step. -/
theorem lemma_2_3 {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Problem n p Ξ) (hP : P.Standing) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P σ α x0 ξ x lam) :
    ∀ t ω, ∀ y ∈ P.X0,
      P.F (x (t + 1) ω) (ξ t ω) + 1 / (2 * σ) * ‖lam (t + 1) ω‖ ^ 2
          + α / 2 * ‖x (t + 1) ω - x t ω‖ ^ 2 ≤
        P.F y (ξ t ω) + 1 / (2 * σ) * ‖projPos (lam t ω + σ • P.G y (ξ t ω))‖ ^ 2
          + α / 2 * (‖y - x t ω‖ ^ 2 - ‖y - x (t + 1) ω‖ ^ 2) := by sorry

end SAPMM.Regret
