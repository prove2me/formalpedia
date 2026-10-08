-- Prove2me | Theorems.Thm_PGLandscape_FiniteHorizon_argmin_separable
-- name    : PGLandscape.FiniteHorizon.argmin_separable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:28.405357+00:00
-- url     : https://prove2.me/theorems/85a81541-14e3-4a47-b460-f996a8e3b674
-- title:
--   (30), App. D.2, p. 40 — separability: θ minimizes B(· | η, J) over Θ iff each θ_h minimizes B_h(· | η, J) over Θ_h
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process and $\Pi_\Theta=\{\pi_\theta:\theta\in\Theta\}$ a parameterized policy class satisfying Condition 3: the states are split into stages $\mathcal S_1,\dots,\mathcal S_H,\mathcal S_{H+1}=\{\tau\}$, $\Theta=\Theta_1\times\cdots\times\Theta_H$, and on $\mathcal S_h$ the action $\pi_\theta(s)$ depends only on the sub-vector $\theta_h$. Let $\eta$ be a finite measure on $\mathcal S$ and $J$ a bounded measurable function. Write $\mathcal B(\bar\theta\mid\eta,J)=\int(T_{\pi_{\bar\theta}}J)\,d\eta$ and $\mathcal B_h(\bar\theta_h\mid\eta,J)=\int_{\mathcal S_h}(T_{\pi_{\bar\theta}}J)\,d\eta$. Then for every $\theta\in\Theta$,
--   $$\theta\in\arg\min_{\bar\theta\in\Theta}\mathcal B(\bar\theta\mid\eta,J)\iff\theta_h\in\arg\min_{\bar\theta_h\in\Theta_h}\mathcal B_h(\bar\theta_h\mid\eta,J)\quad\text{for every }h\in\{1,\dots,H\}.$$
--
--   The weighted policy-iteration objective is a sum of stage objectives, each depending on its own block of parameters, so over a product parameter set it is minimized block by block.
--
--   **Formalization Note** The right-hand side minimizes over the block-$h$ section $\{(\theta_1,\dots,\theta'_h,\dots,\theta_H):\theta'\in\Theta\}$ of $\Theta$ through $\theta$, which is $\Theta_h$ with the other blocks frozen. The page states (30) for $J=J_\pi$; the statement is formalized for every bounded measurable $J$ (it is used with $J=J_{\pi_\theta}$ and with $J=J^*$). The stage-$(H+1)$ term $\int_{\{\tau\}}(T_{\pi_{\bar\theta}}J)\,d\eta=\gamma J(\tau)\eta(\{\tau\})$ does not depend on $\bar\theta$ because $g(\tau,\cdot)=0$ and $P(\cdot\mid\tau,a)=\delta_\tau$; this is why the page's sum stops at $H$. Only Condition 3 is assumed.
-- source:
--   arXiv:1906.01786v3, App. D.2, proof of Theorem 3, (30), p. 40

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions
import Definitions.Def_PGLandscape_FiniteHorizon_Stages

namespace PGLandscape.FiniteHorizon

open MeasureTheory ProbabilityTheory

/-- Separability (30), arXiv:1906.01786v3, App. D.2, p. 40: under Condition 3, for a finite measure
`η` and a bounded measurable `J`, a parameter `θ ∈ Θ` minimizes `θ̄ ↦ B(θ̄ | η, J)` over `Θ` if and
only if, for every stage `h ∈ {1, …, H}`, its sub-vector `θ_h` minimizes `θ̄_h ↦ B_h(θ̄_h | η, J)` over
`Θ_h` (the block-`h` section of `Θ` through `θ`). -/
theorem argmin_separable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) (H : ℕ) (stage : S → ℕ) (τ : S)
    (blk : Fin d → ℕ) (hC3 : Condition3 M H stage τ blk Θ πθ)
    (η : Measure S) [IsFiniteMeasure η] (J : S → ℝ) (hJm : Measurable J)
    (hJb : ∃ C : ℝ, ∀ s, |J s| ≤ C) (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ Θ) :
    (∀ θ' ∈ Θ, PGLandscape.Closure.bellmanObj M (πθ θ).1 η J ≤ PGLandscape.Closure.bellmanObj M (πθ θ').1 η J) ↔
      ∀ h : ℕ, 1 ≤ h → h ≤ H → ∀ x ∈ blockSection blk h Θ θ,
        stageObj M stage h (πθ θ).1 η J ≤ stageObj M stage h (πθ x).1 η J := by sorry

end PGLandscape.FiniteHorizon
