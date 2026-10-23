-- Prove2me | Theorems.Thm_SAPMM_Regret_corollary_2_1
-- name    : SAPMM.Regret.corollary_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:35.245322+00:00
-- url     : https://prove2.me/theorems/9e4de02e-70fd-4428-a08c-d5514fc18a25
-- title:
--   Corollary 2.1, p. 8 (corrected) — pathwise bound (2.11) on Σ_{t<T} G_i(x^t, ξ_t) through λ_i^T and Σ_{t<T} ‖λ^t‖
-- statement:
--   Let $(x^t,\lambda^t)_{t\ge0}$ be a run of PMMSopt (1.5) with parameters $\sigma>0$, $\alpha>0$, started at $x^0\in X_0$ with $\lambda^0=0$, for a problem satisfying the standing assumptions of §1 and (A2)–(A4) (see the definition file). The run is driven by an arbitrary sample path $\xi_0,\xi_1,\dots$; no probabilistic assumption is needed.
--
--   Write $D=2\alpha-p\kappa_g^2\sigma$ and assume $D>0$. Then for every horizon $T\ge0$ and every $i$,
--
--   $$
--   \sum_{t=0}^{T-1}G_i(x^t,\xi_t)\le\frac1\sigma\lambda_i^T+\frac{2\kappa_g\kappa_f}{D}T+\frac{2\sqrt p\,\kappa_g^2}{D}\sum_{t=0}^{T-1}\|\lambda^t\|+\frac{2\sqrt p\,\nu_g\kappa_g^2\sigma}{D}T.
--   $$
--
--   Together with a bound on $\mathbb E\|\lambda^t\|$ this yields the expected constraint-violation bound of Theorem 3.1.
--
--   **Correction.** The paper prints the last two coefficients as $\sqrt p\,\kappa_g^2/D$ and $\sqrt p\,\nu_g\kappa_g^2\sigma/D$. They are doubled here because the corollary combines (2.3) with Lemma 2.4, whose printed bound is too small by exactly these terms (see Lemma 2.4).
--
--   **Formalization Note** The statement is pathwise: it holds for every $\omega$, and (A1) is not assumed (more general than the page, whose proof does not use it). The hypothesis $x^0\in X_0$ corrects Step 0, which prints $x^0\in\mathbb R^n$; it is needed so that $x^0$ lies in $O_0$, where the subgradient and boundedness assumptions apply. Norms are Euclidean on $\mathbb R^n$ and $\mathbb R^p$.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, p. 8, Corollary 2.1, (2.11) (constant corrected)

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- Corollary 2.1, p. 8, (2.11), **corrected**: the last two terms carry `2√p` instead of the
printed `√p` (inherited from the corrected Lemma 2.4). -/
theorem corollary_2_1 {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Problem n p Ξ) (hP : P.Standing) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P σ α x0 ξ x lam)
    (hD : 0 < (2 * α - (p : ℝ) * P.κg ^ 2 * σ)) :
    ∀ (T : ℕ) (i : Fin p) ω,
      ∑ t ∈ Finset.range T, P.G (x t ω) (ξ t ω) i ≤
        1 / σ * lam T ω i + 2 * P.κg * P.κf / (2 * α - (p : ℝ) * P.κg ^ 2 * σ) * T
          + 2 * Real.sqrt p * P.κg ^ 2 / (2 * α - (p : ℝ) * P.κg ^ 2 * σ) * ∑ t ∈ Finset.range T, ‖lam t ω‖
          + 2 * Real.sqrt p * P.νg * P.κg ^ 2 * σ / (2 * α - (p : ℝ) * P.κg ^ 2 * σ) * T := by sorry

end SAPMM.Regret
