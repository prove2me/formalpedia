-- Prove2me | Theorems.Thm_PersonalizedRM_RevenueGap_eq_5
-- name    : PersonalizedRM.RevenueGap.eq_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:56.236624+00:00
-- url     : https://prove2.me/theorems/3366edbe-ffd8-4fbb-bb78-113e60234aad
-- title:
--   (4)–(5), p. 15 (sharpened) — ‖θ̂ − θ∗‖₂ ≤ √(dim)·‖∇f(θ∗)‖_∞/η for an η-strongly convex f minimized over K
-- statement:
--   Let $f : \mathbb R^N \to \mathbb R$ be differentiable, let $K \subseteq \mathbb R^N$ be convex and let $f$ be $\eta$-strongly convex on $K$ with $\eta > 0$ (with respect to the Euclidean norm). Let $\theta^* \in K$, let $\hat\theta \in K$ minimize $f$ over $K$, and suppose $|\partial_k f(\theta^*)| \le g$ for every coordinate $k$. Then
--
--   $$\|\hat\theta - \theta^*\|_2 \ \le\ \frac{\sqrt N\, g}{\eta}.$$
--
--   With $f = \ell_n$, $K$ the $\ell_1$ ball, $N = J(d+1)$ and $g = \|\nabla\ell_n(\theta^*)\|_\infty$, this is the deterministic step (4)–(5) of the paper: strong convexity turns a small gradient at $\theta^*$ into a small estimation error. Plugging in Lemma 1 and the parameter $\eta$ of (6) gives Theorem 1 with its printed constant.
--
--   **Formalization Note.** The printed (5) reads $\|\hat\Delta\|_2 \le 2\sqrt{J(d+1)}\,\|\nabla\ell_n(\theta^*)\|_\infty/\eta$. The statement here has constant $1$ instead of $2$, which is also true (it uses the first-order optimality of the constrained minimizer $\hat\theta$ in addition to (4)); the printed (5) is a weaker corollary. The sharper constant is what makes Theorem 1's printed constant follow from Lemmas 1–2. The statement is generic: any finite coordinate set, any convex set, any differentiable strongly convex function.
-- source:
--   Chen, Owen, Pixton & Simchi-Levi, A statistical learning approach to personalization in revenue management, author manuscript (SSRN 2579462; Management Science 2021), p. 15, (4)–(5)

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory

namespace PersonalizedRM.RevenueGap

/-- (4)–(5), p. 15, sharpened: if `f` is differentiable and `η`-strongly convex on a convex set
`K`, `θhat` minimizes `f` over `K`, `θstar ∈ K`, and every partial derivative of `f` at
`θstar` is at most `g` in absolute value, then
`‖θhat − θstar‖₂ ≤ √(dim) · g / η`. The printed (5) has the factor `2` and is a weaker
corollary. -/
theorem eq_5 {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Set (EuclideanSpace ℝ ι))
    (f : EuclideanSpace ℝ ι → ℝ) (hf : Differentiable ℝ f) (η : ℝ) (hη : 0 < η)
    (hsc : StrongConvexOn K η f) (θstar θhat : EuclideanSpace ℝ ι) (hstar : θstar ∈ K)
    (hhat : θhat ∈ K) (hmin : IsMinOn f K θhat) (g : ℝ)
    (hg : ∀ k, |fderiv ℝ f θstar (EuclideanSpace.single k 1)| ≤ g) :
    ‖θhat - θstar‖ ≤ Real.sqrt (Fintype.card ι) * g / η := by sorry

end PersonalizedRM.RevenueGap
