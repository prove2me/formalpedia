-- Prove2me | Theorems.Thm_SDCA_Smooth_conj_strongly_convex
-- name    : SDCA.Smooth.conj_strongly_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:38.644414+00:00
-- url     : https://prove2.me/theorems/e344d98a-8027-4da9-9e51-2ed5510acaa2
-- title:
--   If $\varphi$ is $(1/\gamma)$-smooth, then $\varphi^*$ is $\gamma$-strongly convex
-- statement:
--   Let $\gamma>0$ and let $\varphi:\mathbb R\to\mathbb R$ be convex and **$(1/\gamma)$-smooth**: $\varphi$ is differentiable and its derivative $\varphi'$ satisfies $|\varphi'(a)-\varphi'(b)|\le\frac1\gamma|a-b|$ for all $a,b\in\mathbb R$. Let $\varphi^*(u)=\sup_z(zu-\varphi(z))\in(-\infty,+\infty]$ be its convex conjugate. Then $\varphi^*$ is $\gamma$-strongly convex: for all $u,v\in\mathbb R$ and $s\in[0,1]$,
--   $$-\varphi^*\big(su+(1-s)v\big)\ \ge\ -s\,\varphi^*(u)-(1-s)\,\varphi^*(v)+\frac{\gamma s(1-s)}{2}(u-v)^2 .$$
--
--   This is the classical duality between smoothness and strong convexity; the paper calls it well known and uses it to feed Lemma 1 in the proof of its linear rate for smooth losses.
--
--   **Formalization Note** The inequality is stated in `EReal` with real coefficients coerced; the conventions $0\cdot(+\infty)=0$ and $(-\infty)+(+\infty)=-\infty$ make it the convex-analysis inequality for an extended-valued $\varphi^*$. Smoothness is the first form of the paper's Definition 1 (a derivative function `φ'` with `HasDerivAt` everywhere and the Lipschitz bound); convexity of $\varphi$ is the paper's standing assumption on the losses (p. 1).
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §1, p. 2, display after Definition 1

import Mathlib
import Definitions.Def_SDCA_Smooth_conj

namespace SDCA.Smooth

/-- §1, p. 2, display after Definition 1 (Shalev-Shwartz–Zhang, arXiv:1209.1873v2): if a convex
`φ : ℝ → ℝ` is `(1/γ)`-smooth (differentiable with a `(1/γ)`-Lipschitz derivative `φ'`), then its
conjugate `φ*` is `γ`-strongly convex: for all `u, v ∈ ℝ` and `s ∈ [0, 1]`,
`−φ*(s u + (1 − s) v) ≥ −s φ*(u) − (1 − s) φ*(v) + γ s (1 − s)/2 · (u − v)²` (in `EReal`). -/
theorem conj_strongly_convex (φ φ' : ℝ → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hconv : ConvexOn ℝ Set.univ φ)
    (hderiv : ∀ a : ℝ, HasDerivAt φ (φ' a) a)
    (hsmooth : ∀ a b : ℝ, |φ' a - φ' b| ≤ (1 / γ) * |a - b|) :
    ∀ u v : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      -SDCA.Lipschitz.conj φ (s * u + (1 - s) * v) ≥
        -(((s : ℝ) : EReal) * SDCA.Lipschitz.conj φ u) - ((1 - s : ℝ) : EReal) * SDCA.Lipschitz.conj φ v +
          ((γ * s * (1 - s) / 2 * (u - v) ^ 2 : ℝ) : EReal) := by sorry

end SDCA.Smooth
