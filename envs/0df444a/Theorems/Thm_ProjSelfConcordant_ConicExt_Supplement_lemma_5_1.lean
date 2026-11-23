-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_Supplement_lemma_5_1
-- name    : ProjSelfConcordant.ConicExt.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:21:10.494169+00:00
-- url     : https://prove2.me/theorems/0a66b035-9abb-475e-bd0c-1de31a42b20c
-- title:
--   Lemma 5.1, p. 13 — q″ − q′wᵀ − wq′ᵀ ≻ 0 for some co-vector field w implies quasi-convexity
-- statement:
--   Let $D\subset\mathbb R^n$ be an open convex set and $q:D\to\mathbb R$ a function of class $C^2$. Suppose there is a co-vector field $w$ on $D$, that is, an arbitrary assignment of a linear functional $w(x)$ to each $x\in D$ (no continuity is assumed), such that
--   $$q''(x)-q'(x)\,w(x)^T-w(x)\,q'(x)^T\succ0\qquad\text{for all }x\in D,$$
--   i.e. $q''(x)[h,h]-2\,q'(x)[h]\,w(x)[h]>0$ for every $x\in D$ and $h\neq0$. Then $q$ is quasi-convex on $D$: for all $x,y\in D$ and $\lambda\in(0,1)$,
--   $$q(\lambda x+(1-\lambda)y)\le\max(q(x),q(y)).$$
--
--   The lemma is the tool used in Lemma 5.3 to show that the function $q_p$ defining the dual has at most one critical point.
--
--   **Formalization Note** Quasi-convexity is Mathlib's `QuasiconvexOn ℝ D q` (every sublevel set within $D$ is convex), which on a convex $D$ is equivalent to the inequality above. The co-vector field is a function into continuous linear functionals with no regularity assumption.
--
--   Differences from the source:
--   - encoding: q : D → ℝ → a total function on ℝⁿ that is C² on D; reason: only values on the open set D enter the hypotheses and the conclusion
--   - encoding: functions and derivatives on open subsets of ℝⁿ → total functions on EuclideanSpace ℝ (Fin n), with Fréchet derivatives evaluated on the stated open domains; reason: every source function extends outside its domain; derivatives at interior points depend only on local values, and the Euclidean inner product identifies covectors with gradients when needed
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 13, Lemma 5.1 (and the definition of quasi-convexity in its proof)

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Barrier

namespace ProjSelfConcordant.ConicExt.Supplement

/-- Lemma 5.1, p. 13: let `D ⊂ ℝⁿ` be open and convex and `q` of class `C²` on `D`. If there is a
co-vector field `w` on `D` (with no regularity) such that
`q″(x) − q′(x) w(x)ᵀ − w(x) q′(x)ᵀ ≻ 0` for all `x ∈ D`, then `q` is quasi-convex on `D`. -/
theorem lemma_5_1 {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (q : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiffOn ℝ 2 q D)
    (w : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (hw : ∀ x ∈ D, ∀ h : EuclideanSpace ℝ (Fin n), h ≠ 0 →
      0 < d2 q x h h - fderiv ℝ q x h * w x h - w x h * fderiv ℝ q x h) :
    QuasiconvexOn ℝ D q := by sorry

end ProjSelfConcordant.ConicExt.Supplement
