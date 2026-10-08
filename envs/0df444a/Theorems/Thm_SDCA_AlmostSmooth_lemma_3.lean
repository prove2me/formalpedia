-- Prove2me | Theorems.Thm_SDCA_AlmostSmooth_lemma_3
-- name    : SDCA.AlmostSmooth.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:06:15.195348+00:00
-- url     : https://prove2.me/theorems/52002a4e-b46d-413c-9172-0dabfd4b4cb8
-- title:
--   Lemma 3 — the conjugate of an $L$-Lipschitz function is $+\infty$ outside $[-L,L]$
-- statement:
--   Let $\varphi:\mathbb R\to\mathbb R$ be $L$-Lipschitz, that is $|\varphi(a)-\varphi(b)|\le L|a-b|$ for all $a,b\in\mathbb R$, and let $\varphi^*(\alpha)=\sup_z(z\alpha-\varphi(z))$ be its convex conjugate. Then for every $\alpha$ with $|\alpha|>L$,
--   $$
--   \varphi^*(\alpha)=+\infty .
--   $$
--
--   Consequently a feasible dual variable for $L$-Lipschitz losses has all coordinates in $[-L,L]$, which is how the variance term of Lemma 6 is bounded.
--
--   **Formalization Note** The conjugate takes values in `EReal` and the conclusion is equality with `⊤`. No convexity of $\varphi$ is assumed.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, p. 15, Lemma 3

import Mathlib
import Definitions.Def_SDCA_AlmostSmooth_Model

namespace SDCA.AlmostSmooth

/-- Lemma 3 (p. 15): if `φ : ℝ → ℝ` is `L`-Lipschitz, then `φ*(α) = +∞` whenever `|α| > L`. -/
theorem lemma_3 (φ : ℝ → ℝ) (L : ℝ) (hL : ∀ a b : ℝ, |φ a - φ b| ≤ L * |a - b|) (α : ℝ)
    (hα : L < |α|) : SDCA.Lipschitz.conj φ α = ⊤ := by sorry

end SDCA.AlmostSmooth
