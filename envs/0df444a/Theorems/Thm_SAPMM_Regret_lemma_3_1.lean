-- Prove2me | Theorems.Thm_SAPMM_Regret_lemma_3_1
-- name    : SAPMM.Regret.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:57.382024+00:00
-- url     : https://prove2.me/theorems/4528eaf1-d48d-4cef-a730-2fdf58db36b7
-- title:
--   Lemma 3.1, p. 13 — pathwise objective bound (3.3) for PMMSopt
-- statement:
--   Let $(x^t,\lambda^t)_{t\ge0}$ be a run of PMMSopt (1.5) with parameters $\sigma>0$, $\alpha>0$, started at $x^0\in X_0$ with $\lambda^0=0$, for a problem satisfying the standing assumptions of §1 and (A2)–(A4) (see the definition file). The run is driven by an arbitrary sample path $\xi_0,\xi_1,\dots$; no probabilistic assumption is needed.
--
--   Then for every horizon $T\ge0$ and every $x\in X_0$,
--
--   $$
--   \sum_{t=0}^{T-1}F(x^t,\xi_t)\le\sum_{t=0}^{T-1}F(x,\xi_t)+\frac{\kappa_f^2}{2\alpha}T+\frac\alpha2D_0^2+\frac\sigma2\nu_g^2T+\sum_{t=0}^{T-1}\langle\lambda^t,G(x,\xi_t)\rangle.
--   $$
--
--   Taking $x$ feasible and expectations, the last sum has nonpositive expectation, which gives the objective regret bound of Theorem 3.2.
--
--   **Formalization Note** The statement is pathwise: it holds for every $\omega$, and (A1) is not assumed (more general than the page, whose proof does not use it). The hypothesis $x^0\in X_0$ corrects Step 0, which prints $x^0\in\mathbb R^n$; it is needed so that $x^0$ lies in $O_0$, where the subgradient and boundedness assumptions apply. Norms are Euclidean on $\mathbb R^n$ and $\mathbb R^p$.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, p. 13, Lemma 3.1, (3.3)

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- Lemma 3.1, p. 13, (3.3): pathwise objective bound. -/
theorem lemma_3_1 {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Problem n p Ξ) (hP : P.Standing) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P σ α x0 ξ x lam) :
    ∀ (T : ℕ) ω, ∀ y ∈ P.X0,
      ∑ t ∈ Finset.range T, P.F (x t ω) (ξ t ω) ≤
        ∑ t ∈ Finset.range T, P.F y (ξ t ω) + P.κf ^ 2 / (2 * α) * T + α / 2 * P.D0 ^ 2
          + σ / 2 * P.νg ^ 2 * T
          + ∑ t ∈ Finset.range T, inner ℝ (lam t ω) (P.G y (ξ t ω)) := by sorry

end SAPMM.Regret
