-- Prove2me | Theorems.Thm_PGLandscape_FiniteHorizon_stationary_iff_stagewise
-- name    : PGLandscape.FiniteHorizon.stationary_iff_stagewise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:14.387066+00:00
-- url     : https://prove2.me/theorems/de935ac1-521e-4e88-84ce-80129aaed357
-- title:
--   (31), App. D.2, p. 40 — θ is a stationary point of ℓ on Θ iff each θ_h is a stationary point of B_h(· | η_{π_θ}, J_{π_θ}) on Θ_h
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process and $\Pi_\Theta=\{\pi_\theta:\theta\in\Theta\}$ a parameterized policy class over a convex $\Theta\subseteq\mathbb R^d$ satisfying Condition 0 (differentiability) and Condition 3 (stages $\mathcal S_1,\dots,\mathcal S_{H+1}$, $\Theta=\Theta_1\times\cdots\times\Theta_H$, and on $\mathcal S_h$ the action $\pi_\theta(s)$ depends only on $\theta_h$). Let $\ell(\theta)=\ell(\pi_\theta)$ and $\mathcal B_h(\bar\theta_h\mid\eta,J)=\int_{\mathcal S_h}(T_{\pi_{\bar\theta}}J)\,d\eta$. Then for every $\theta\in\Theta$ the following are equivalent:
--   1. $\theta$ is a stationary point of $\ell$ on $\Theta$: $\langle\nabla\ell(\theta),\theta'-\theta\rangle\ge0$ for all $\theta'\in\Theta$;
--   2. for every stage $h\in\{1,\dots,H\}$, $\theta_h$ is a stationary point of $\bar\theta_h\mapsto\mathcal B_h(\bar\theta_h\mid\eta_{\pi_\theta},J_{\pi_\theta})$ on $\Theta_h$:
--   $$\Big[\frac{\partial}{\partial\bar\theta_h}\mathcal B_h(\bar\theta_h\mid\eta_{\pi_\theta},J_{\pi_\theta})\Big|_{\bar\theta_h=\theta_h}\Big](\theta'_h-\theta_h)\ge0\qquad\forall\theta'_h\in\Theta_h .$$
--
--   Through the policy gradient theorem, first-order stationarity of the multi-period objective decomposes into first-order stationarity of $H$ single-period problems, one per stage.
--
--   **Formalization Note** Stationarity (Definition 1) includes differentiability at the point. Item 2 is stated with the full gradient of $\bar\theta\mapsto\mathcal B_h(\bar\theta\mid\eta_{\pi_\theta},J_{\pi_\theta})$ on $\mathbb R^d$ and the block-$h$ section $\{(\theta_1,\dots,\theta'_h,\dots,\theta_H):\theta'\in\Theta\}$ of $\Theta$ through $\theta$; since $\mathcal B_h$ depends on $\bar\theta$ only through block $h$, this is the page's block-restricted condition. Condition 0 is the joint form of the definition file (needed by Lemma 6, which the page invokes for (31)).
-- source:
--   arXiv:1906.01786v3, App. D.2, proof of Theorem 3, (31), p. 40

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions
import Definitions.Def_PGLandscape_FiniteHorizon_Stages

namespace PGLandscape.FiniteHorizon

open MeasureTheory ProbabilityTheory

/-- Single period characterization of stationary points (31), arXiv:1906.01786v3, App. D.2, p. 40:
under Conditions 0 and 3, `θ ∈ Θ` is a stationary point of `ℓ` on `Θ` if and only if, for every
stage `h ∈ {1, …, H}`, `θ_h` is a stationary point of `θ̄_h ↦ B_h(θ̄_h | η_{π_θ}, J_{π_θ})` on `Θ_h`
(stated with the full gradient on the block-`h` section of `Θ` through `θ`). -/
theorem stationary_iff_stagewise {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ)
    (H : ℕ) (stage : S → ℕ) (τ : S) (blk : Fin d → ℕ)
    (hC0 : PGLandscape.Closure.Condition0 M Θ πθ) (hC3 : Condition3 M H stage τ blk Θ πθ)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ Θ) :
    PGLandscape.Closure.IsStationary (PGLandscape.Closure.lossParam M πθ) Θ θ ↔
      ∀ h : ℕ, 1 ≤ h → h ≤ H →
        PGLandscape.Closure.IsStationary
          (fun θbar => stageObj M stage h (πθ θbar).1 (PGLandscape.Closure.occupancy M (πθ θ)) (PGLandscape.Closure.costToGo M (πθ θ)))
          (blockSection blk h Θ θ) θ := by sorry

end PGLandscape.FiniteHorizon
