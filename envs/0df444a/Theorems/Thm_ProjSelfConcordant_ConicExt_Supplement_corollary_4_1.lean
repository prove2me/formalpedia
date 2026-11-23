-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_Supplement_corollary_4_1
-- name    : ProjSelfConcordant.ConicExt.Supplement.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:19:42.214643+00:00
-- url     : https://prove2.me/theorems/c8f4433a-b165-4f5b-ba53-e38718942a53
-- title:
--   Corollary 4.1, p. 10 — two-sided bounds on the boundary gauges σₓ(h), πₓ(h) by f′(x)[h] and √G(x)[h, h]
-- statement:
--   Let $X\subset\mathbb R^n$ be a regular convex set (closed, convex, with nonempty interior $X^o$, containing no line), let $\nu\ge2$, and let $f$ be a projectively self-concordant barrier on $X$ with parameter $\gamma=(\nu-2)/\sqrt{\nu-1}$. Write $G(x)[h,h]=f''(x)[h,h]-(f'(x)[h])^2$ for the affine metric and
--   $$\sigma_x(h)=\inf\{t^{-1}\mid t>0,\ x+th\in X\},\qquad \pi_x(h)=\max(\sigma_x(h),\sigma_x(-h))$$
--   for the boundary gauges. Then for all $x\in X^o$ and all $h\in\mathbb R^n$,
--   $$\max\Bigl(0,\ f'(x)[h]+\frac{\sqrt{G(x)[h,h]}}{\sqrt{\nu-1}}\Bigr)\le\sigma_x(h)\le\max\Bigl(0,\ f'(x)[h]+\sqrt{\nu-1}\sqrt{G(x)[h,h]}\Bigr),$$
--   $$|f'(x)[h]|+\frac{\sqrt{G(x)[h,h]}}{\sqrt{\nu-1}}\le\pi_x(h)\le|f'(x)[h]|+\sqrt{\nu-1}\sqrt{G(x)[h,h]}.$$
--
--   The bounds express the distance from $x$ to the boundary of $X$ in every direction through the first two derivatives of the barrier at $x$; they include unbounded directions ($\sigma_x(h)=0$), $h=0$, and the case $\nu=2$, $\gamma=0$.
--
--   **Formalization Note** $f'(x)[h]$ is `fderiv ℝ f x h`; the infimum is a real `sInf`, which is the genuine infimum for $x\in X^o$. The hypothesis $\nu\ge2$ is the range of $\nu$ for which $\gamma=(\nu-2)/\sqrt{\nu-1}$ is a real number $\ge0$, as Definition 1.4 requires.
--
--   Differences from the source:
--   - encoding: γ = (ν − 2)/√(ν − 1) with γ ≥ 0 required by Definition 1.4 → explicit hypothesis 2 ≤ ν; reason: exactly the ν for which the formula defines a real γ ≥ 0; Lean's √ of a negative number is 0, so the range must be written out
--   - encoding: functions and derivatives on open subsets of ℝⁿ → total functions on EuclideanSpace ℝ (Fin n), with Fréchet derivatives evaluated on the stated open domains; reason: every source function extends outside its domain; derivatives at interior points depend only on local values, and the Euclidean inner product identifies covectors with gradients when needed
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 10, Corollary 4.1 (with equation (5), p. 9)

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Barrier

namespace ProjSelfConcordant.ConicExt.Supplement

/-- Corollary 4.1, p. 10: for a projectively self-concordant barrier `f` on a regular convex set
`X ⊂ ℝⁿ` with parameter `γ = (ν − 2)/√(ν − 1)`, for all `x ∈ Xᵒ` and `h ∈ ℝⁿ`,
`max(0, f′(x)[h] + √G(x)[h,h]/√(ν−1)) ≤ σₓ(h) ≤ max(0, f′(x)[h] + √(ν−1)√G(x)[h,h])` and
`|f′(x)[h]| + √G(x)[h,h]/√(ν−1) ≤ πₓ(h) ≤ |f′(x)[h]| + √(ν−1)√G(x)[h,h]`. -/
theorem corollary_4_1 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : RegularConvexSet X) (f : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 2 ≤ ν)
    (hf : ProjBarrier ((ν - 2) / Real.sqrt (ν - 1)) X f) :
    ∀ x ∈ interior X, ∀ h : EuclideanSpace ℝ (Fin n),
      (max 0 (fderiv ℝ f x h + Real.sqrt (affMetric f x h h) / Real.sqrt (ν - 1))
          ≤ sigmaGauge X x h ∧
        sigmaGauge X x h
          ≤ max 0 (fderiv ℝ f x h + Real.sqrt (ν - 1) * Real.sqrt (affMetric f x h h))) ∧
      (|fderiv ℝ f x h| + Real.sqrt (affMetric f x h h) / Real.sqrt (ν - 1)
          ≤ piGauge X x h ∧
        piGauge X x h
          ≤ |fderiv ℝ f x h| + Real.sqrt (ν - 1) * Real.sqrt (affMetric f x h h)) := by sorry

end ProjSelfConcordant.ConicExt.Supplement
