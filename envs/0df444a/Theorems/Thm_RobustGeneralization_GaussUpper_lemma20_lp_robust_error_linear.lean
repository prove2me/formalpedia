-- Prove2me | Theorems.Thm_RobustGeneralization_GaussUpper_lemma20_lp_robust_error_linear
-- name    : RobustGeneralization.GaussUpper.lemma20_lp_robust_error_linear
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:27:38.133441+00:00
-- url     : https://prove2.me/theorems/7a13677e-6293-4339-afcb-2bc3f10c59c6
-- title:
--   Lemma 20 — ℓ_p^ε-robust error of f_ŵ ≤ exp(−(⟨ŵ, θ⋆⟩ − ε‖ŵ‖*_p)²/(2σ²)) when ⟨ŵ, θ⋆⟩ ≥ ε‖ŵ‖*_p
-- statement:
--   Consider the $(\theta^\star,\sigma)$-Gaussian model with $\sigma>0$. Let $p\in[1,\infty]$ and $\varepsilon\ge0$ be robustness parameters, let $\|\cdot\|_p^*$ be the dual norm of $\|\cdot\|_p$, and let $\widehat w$ be a unit vector ($\|\widehat w\|_2=1$) with $\langle\widehat w,\theta^\star\rangle\ge\varepsilon\|\widehat w\|_p^*$. Then the linear classifier $f_{\widehat w}$ has $\ell_p^\varepsilon$-robust classification error at most
--
--   $$\exp\left(-\frac{\big(\langle\widehat w,\theta^\star\rangle-\varepsilon\|\widehat w\|_p^*\big)^2}{2\sigma^2}\right).$$
--
--   For a linear classifier, an $\ell_p$ adversary of budget $\varepsilon$ can shift the margin by exactly $\varepsilon\|\widehat w\|_p^*$; the lemma turns alignment with $\theta^\star$ beyond that shift into a bound on the robust error. With $p=\infty$ the dual norm is $\|\widehat w\|_1$, which is how Theorem 21 uses it.
--
--   **Formalization Note** $p$ ranges over the extended reals $[1,\infty]$, including $p=\infty$. The $\ell_p^\varepsilon$ ball is $\{x':\|x'-x\|_p\le\varepsilon\}$ with the `PiLp p` norm, and $\|w\|_p^*$ is the supremum of $\langle w,v\rangle$ over $\|v\|_p\le1$, a nonempty bounded set.
-- source:
--   Schmidt et al., Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 25, Lemma 20

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussUpper

/-- **Lemma 20** (p. 25). In the `(θ⋆, σ)`-Gaussian model, let `p ≥ 1`, `ε ≥ 0`, and let `ŵ` be a
unit vector with `⟨ŵ, θ⋆⟩ ≥ ε‖ŵ‖*_p`, where `‖·‖*_p` is the dual norm of `‖·‖_p`. Then `f_ŵ` has
ℓ_p^ε-robust classification error at most `exp(-(⟨ŵ, θ⋆⟩ - ε‖ŵ‖*_p)²/(2σ²))`. -/
theorem lemma20_lp_robust_error_linear (d : ℕ) (θ : E d) (σ : ℝ) (hσ : 0 < σ) (p : ℝ≥0∞)
    (hp : 1 ≤ p) (ε : ℝ) (hε : 0 ≤ ε) (w : E d) (hw : ‖w‖ = 1)
    (hwθ : ε * dualNorm p w ≤ inner ℝ w θ) :
    robustErrP p (gaussModel θ σ) (linClf w) ε ≤
      ENNReal.ofReal
        (Real.exp (-(inner ℝ w θ - ε * dualNorm p w) ^ 2 / (2 * σ ^ 2))) := by sorry

end RobustGeneralization.GaussUpper
