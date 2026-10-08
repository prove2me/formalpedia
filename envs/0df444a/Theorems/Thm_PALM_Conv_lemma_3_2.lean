-- Prove2me | Theorems.Thm_PALM_Conv_lemma_3_2
-- name    : PALM.Conv.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:48.012868+00:00
-- url     : https://prove2.me/theorems/4482577d-d8a9-4df6-8b56-6a2e477b9704
-- title:
--   Lemma 3.2 (Sufficient decrease) — h(u⁺) + σ(u⁺) ≤ h(u) + σ(u) − ½(t − L_h)‖u⁺ − u‖² for a proximal-gradient step
-- statement:
--   Let $h:\mathbb R^d\to\mathbb R$ be continuously differentiable with $L_h$-Lipschitz gradient, and let $\sigma:\mathbb R^d\to(-\infty,+\infty]$ be proper and lower semicontinuous with $\inf_{\mathbb R^d}\sigma>-\infty$. Fix $t>L_h$. For every $u\in\operatorname{dom}\sigma$ and every
--   $$u^+\in\operatorname{prox}^\sigma_t\Big(u-\frac1t\nabla h(u)\Big)$$
--   (the prox map (2.2), with weight $t/2$), one has
--   $$h(u^+)+\sigma(u^+)\le h(u)+\sigma(u)-\frac12(t-L_h)\|u^+-u\|^2.$$
--
--   This is the sufficient decrease of one proximal-gradient step in the nonconvex setting; applied once in each block it yields the descent property of PALM (Lemma 3.3).
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, $L_h\ge0$ is an `NNReal` with `LipschitzWith`, and the inequality is stated in `EReal`; since $\sigma(u)$ is finite the subtraction of the real number $\frac12(t-L_h)\|u^+-u\|^2$ is the ordinary one. The hypotheses "lower semicontinuous" and "$\inf\sigma>-\infty$" are kept as on the page, although the inequality itself does not use them (they guarantee that $u^+$ exists).
-- source:
--   Bolte, Sabach, Teboulle, Proximal alternating linearized minimization for nonconvex and nonsmooth problems, Math. Program. 146 (2014), doi:10.1007/s10107-013-0701-9 (source: author version), p. 13, Lemma 3.2, (3.9)–(3.10)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ProxAltMin_Conv_Setting
import Definitions.Def_PALM_Conv_Setting
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL ProxAltMin.Conv PALM.Conv
open Filter Topology

namespace PALM.Conv

/-- Lemma 3.2 (Sufficient decrease property), p. 13: for a `C¹` function `h` with
`Lₕ`-Lipschitz gradient, a proper lsc `σ` bounded below, `t > Lₕ`, `u ∈ dom σ` and
`u⁺ ∈ prox^σ_t(u - (1/t)∇h(u))`, one has
`h(u⁺) + σ(u⁺) ≤ h(u) + σ(u) - (1/2)(t - Lₕ)‖u⁺ - u‖²`. -/
theorem lemma_3_2 {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℝ) (Lh : NNReal)
    (hh : ContDiff ℝ 1 h) (hLip : LipschitzWith Lh (gradient h))
    (σ : EuclideanSpace ℝ (Fin d) → EReal) (hσp : IsProperFn σ) (hσl : LowerSemicontinuous σ)
    (hσinf : ∃ c : ℝ, ∀ u, (c : EReal) ≤ σ u) (t : ℝ) (ht : (Lh : ℝ) < t)
    (u uplus : EuclideanSpace ℝ (Fin d)) (hu : σ u ≠ ⊤)
    (hplus : uplus ∈ proxSet σ t (u - (1 / t) • gradient h u)) :
    ((h uplus : ℝ) : EReal) + σ uplus ≤
      ((h u : ℝ) : EReal) + σ u - ((1 / 2 * (t - Lh) * ‖uplus - u‖ ^ 2 : ℝ) : EReal) := by sorry

end PALM.Conv
