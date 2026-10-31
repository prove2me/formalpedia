-- Prove2me | Theorems.Thm_SAPMM_Regret_lemma_2_4
-- name    : SAPMM.Regret.lemma_2_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:31.511026+00:00
-- url     : https://prove2.me/theorems/01b3e962-aeb6-4789-8637-a5262d8e275f
-- title:
--   Lemma 2.4, p. 7 (corrected) — ‖x^{t+1} − x^t‖ ≤ (2κ_f + 2√p κ_g‖λ^t‖ + 2ν_g√p κ_g σ)/(2α − pκ_g²σ)
-- statement:
--   Let $(x^t,\lambda^t)_{t\ge0}$ be a run of PMMSopt (1.5) with parameters $\sigma>0$, $\alpha>0$, started at $x^0\in X_0$ with $\lambda^0=0$, for a problem satisfying the standing assumptions of §1 and (A2)–(A4) (see the definition file). The run is driven by an arbitrary sample path $\xi_0,\xi_1,\dots$; no probabilistic assumption is needed.
--
--   If $2\alpha-p\kappa_g^2\sigma>0$, then for every $t\ge0$,
--
--   $$
--   \|x^{t+1}-x^t\|\le\frac{2\kappa_f+2\sqrt p\,\kappa_g\|\lambda^t\|+2\nu_g\sqrt p\,\kappa_g\sigma}{2\alpha-p\kappa_g^2\sigma}.
--   $$
--
--   The bound controls the movement of the primal iterates by the size of the current multiplier, and is what turns the constraint-sum bound (2.3) into Corollary 2.1.
--
--   **Correction.** The paper prints $\frac{1}{2\alpha-p\kappa_g^2\sigma}[2\kappa_f+\sqrt p\,\kappa_g\|\lambda^t\|+\nu_g\sqrt p\,\kappa_g\sigma]$. Its chain (2.10) uses $\|B\|+\|A\|\le\|\lambda^t\|+\sigma\|G(x^t,\xi_t)\|+\|B-A\|$, whereas only $\|B\|+\|A\|\le2\|B\|+\|B-A\|$ holds; redoing the last steps doubles the last two terms. The printed bound fails at the one-step state $n=p=1$, $X_0=[-1,1]$, $F\equiv0$, $G(x,\xi)=x$, $\alpha=1$, $\sigma=10^{-3}$, $\kappa_f=10^{-3}$, $\kappa_g=1$, $\nu_g=3/2$, $x^t=0$, $\lambda^t=1/2$: there $x^{t+1}\approx-0.4995$, but the printed right-hand side is $\approx0.252$.
--
--   **Formalization Note** The statement is pathwise: it holds for every $\omega$, and (A1) is not assumed (more general than the page, whose proof does not use it). The hypothesis $x^0\in X_0$ corrects Step 0, which prints $x^0\in\mathbb R^n$; it is needed so that $x^0$ lies in $O_0$, where the subgradient and boundedness assumptions apply. Norms are Euclidean on $\mathbb R^n$ and $\mathbb R^p$.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, p. 7, Lemma 2.4, (2.7) (proof (2.10), p. 8; constant corrected)

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- Lemma 2.4, p. 7, (2.7), **corrected**: the printed bound `[2κf + √p κg‖λ^t‖ + νg√p κg σ]`
has its last two terms doubled (the chain (2.10) drops a factor 2). -/
theorem lemma_2_4 {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Problem n p Ξ) (hP : P.Standing) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P σ α x0 ξ x lam)
    (hD : 0 < (2 * α - (p : ℝ) * P.κg ^ 2 * σ)) :
    ∀ t ω, ‖x (t + 1) ω - x t ω‖ ≤
      (2 * P.κf + 2 * Real.sqrt p * P.κg * ‖lam t ω‖ + 2 * P.νg * Real.sqrt p * P.κg * σ)
        / (2 * α - (p : ℝ) * P.κg ^ 2 * σ) := by sorry

end SAPMM.Regret
