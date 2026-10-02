-- Prove2me | Theorems.Thm_RobustGeneralization_GaussUpper_theorem21_robust_error_upper_bound
-- name    : RobustGeneralization.GaussUpper.theorem21_robust_error_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:27:58.963671+00:00
-- url     : https://prove2.me/theorems/6fa5ae9e-10cc-4d33-9d60-9b7c9f271db0
-- title:
--   Theorem 21 — f_ŵ has ℓ∞^ε-robust error ≤ β w.p. ≥ 1 − 2exp(−d/(8(σ²+1))) if ε ≤ (2√n−1)/(2√n+4σ) − σ√(2 log 1/β)/√d
-- statement:
--   Let $(x_1,y_1),\dots,(x_n,y_n)\in\mathbb R^d\times\{\pm1\}$ be drawn i.i.d. from a $(\theta^\star,\sigma)$-Gaussian model with $\|\theta^\star\|_2=\sqrt d$ and $\sigma>0$. Let $\bar z=\frac1n\sum_{i=1}^ny_ix_i$ and $\widehat w=\bar z/\|\bar z\|_2$. Let $\beta>0$ and let $\varepsilon$ satisfy
--
--   $$\varepsilon\le\frac{2\sqrt n-1}{2\sqrt n+4\sigma}-\frac{\sigma\sqrt{2\log(1/\beta)}}{\sqrt d}.$$
--
--   Then with probability at least $1-2\exp\big(-\frac{d}{8(\sigma^2+1)}\big)$ over the sample, the linear classifier $f_{\widehat w}$ has $\ell_\infty^\varepsilon$-robust classification error at most $\beta$.
--
--   This is the paper's general robust upper bound: it quantifies how the robustness budget $\varepsilon$ that the class-weighted mean tolerates grows with the number of samples $n$. Corollary 22 specializes it to $\beta=0.01$.
--
--   **Formalization Note** The conclusion is a bound on the failure set: for every such $\varepsilon$ and $\beta$, the samples on which the robust error exceeds $\beta$ have probability at most $2\exp(-d/(8(\sigma^2+1)))$. The hypothesis $\beta>0$ is added: at $\beta=0$ Lean's $\log(1/0)=0$ would make the claim "error $\le0$" under a non-vacuous condition. For $\beta\ge1$ the square root of $2\log(1/\beta)\le0$ is $0$ and the claim is trivial. No hypothesis on $n$ is needed: for $n=0$ the condition forces $\varepsilon<0$, where the perturbation set is empty. The $\ell_\infty$ ball is coordinatewise.
-- source:
--   Schmidt et al., Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 26, Theorem 21

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussUpper

/-- **Theorem 21** (p. 26). For `n` i.i.d. samples of the `(θ⋆, σ)`-Gaussian model with
`‖θ⋆‖₂ = √d` and `ŵ = z̄/‖z̄‖₂`, `z̄ = (1/n) ∑ yᵢ xᵢ`: with probability at least
`1 - 2 exp(-d/(8(σ² + 1)))` the classifier `f_ŵ` has ℓ∞^ε-robust classification error at most `β`
if `ε ≤ (2√n - 1)/(2√n + 4σ) - σ√(2 log(1/β))/√d`. Stated as a bound on the failure set, for
every such `ε` and `β`; `0 < β` is added. -/
theorem theorem21_robust_error_upper_bound (d n : ℕ) (θ : E d) (hθ : ‖θ‖ = Real.sqrt d)
    (σ : ℝ) (hσ : 0 < σ) (ε β : ℝ) (hβ : 0 < β)
    (hε : ε ≤ (2 * Real.sqrt n - 1) / (2 * Real.sqrt n + 4 * σ) -
      σ * Real.sqrt (2 * Real.log (1 / β)) / Real.sqrt d) :
    (Measure.pi fun _ : Fin n => gaussModel θ σ)
        {S | ENNReal.ofReal β < robustErr (gaussModel θ σ) (linClf (what S)) ε} ≤
      ENNReal.ofReal (2 * Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by sorry

end RobustGeneralization.GaussUpper
