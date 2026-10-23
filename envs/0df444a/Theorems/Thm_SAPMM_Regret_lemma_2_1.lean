-- Prove2me | Theorems.Thm_SAPMM_Regret_lemma_2_1
-- name    : SAPMM.Regret.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:29.906236+00:00
-- url     : https://prove2.me/theorems/9ab737fc-7c05-4b20-8523-8a03c1925c6e
-- title:
--   Lemma 2.1, p. 5 — PMMSopt multipliers: ‖λ^{t+1}‖² ≤ ‖λ^t‖² + 2σ⟨λ^t, G(x^{t+1}, ξ_t)⟩ + σ²ν_g² and |‖λ^{t+1}‖ − ‖λ^t‖| ≤ σν_g
-- statement:
--   Let $(x^t,\lambda^t)_{t\ge0}$ be a run of PMMSopt (1.5) with parameters $\sigma>0$, $\alpha>0$, started at $x^0\in X_0$ with $\lambda^0=0$, for a problem satisfying the standing assumptions of §1 and (A2)–(A4) (see the definition file). The run is driven by an arbitrary sample path $\xi_0,\xi_1,\dots$; no probabilistic assumption is needed.
--
--   Then for every $t\ge0$,
--
--   $$
--   \|\lambda^{t+1}\|^2\le\|\lambda^t\|^2+2\sigma\langle\lambda^t,G(x^{t+1},\xi_t)\rangle+\sigma^2\nu_g^2
--   $$
--
--   and
--
--   $$
--   \|\lambda^t\|-\sigma\nu_g\le\|\lambda^{t+1}\|\le\|\lambda^t\|+\sigma\nu_g.
--   $$
--
--   The first inequality is the one-step recursion of the squared multiplier norm; the second says the multipliers move by at most $\sigma\nu_g$ per step, which is the bounded-increment hypothesis of the drift lemma.
--
--   **Formalization Note** The statement is pathwise: it holds for every $\omega$, and (A1) is not assumed (more general than the page, whose proof does not use it). The hypothesis $x^0\in X_0$ corrects Step 0, which prints $x^0\in\mathbb R^n$; it is needed so that $x^0$ lies in $O_0$, where the subgradient and boundedness assumptions apply. Norms are Euclidean on $\mathbb R^n$ and $\mathbb R^p$.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, p. 5, Lemma 2.1, (2.1)–(2.2)

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- Lemma 2.1, p. 5: (2.1) and (2.2) along every path of PMMSopt. -/
theorem lemma_2_1 {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Problem n p Ξ) (hP : P.Standing) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P σ α x0 ξ x lam) :
    ∀ t ω, ‖lam (t + 1) ω‖ ^ 2 ≤ ‖lam t ω‖ ^ 2
        + 2 * σ * inner ℝ (lam t ω) (P.G (x (t + 1) ω) (ξ t ω)) + σ ^ 2 * P.νg ^ 2 ∧
      ‖lam t ω‖ - σ * P.νg ≤ ‖lam (t + 1) ω‖ ∧ ‖lam (t + 1) ω‖ ≤ ‖lam t ω‖ + σ * P.νg := by sorry

end SAPMM.Regret
