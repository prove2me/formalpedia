-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_10
-- name    : TiltedCvx.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:30:23.136378+00:00
-- url     : https://prove2.me/theorems/4092eccb-07be-40e1-a316-d2044c355399
-- title:
--   Theorem 10 — values on $\operatorname{ri}(K)$ determine $f$ on $\overline K$
-- statement:
--   Let $\gamma\in(0,1]$ and let $f,g:\mathbb R^d\to\overline{\mathbb R}$ be proper, lower semicontinuous and $\gamma$–tilted convex. Set $K:=\operatorname{dom}(f)$. If $f=g$ on $\operatorname{ri}(K)$, then
--
--   $$
--   f=g\quad\text{on the closure }\overline K .
--   $$
--
--   Moreover, $f=\operatorname{lsc}\big(f|_{\operatorname{ri}(K)}\big)$ on all of $\mathbb R^d$.
--
--   As for proper lsc convex functions, the values on the relative interior of the domain determine the function.
--
--   **Formalization Note** "Proper, lsc and $\gamma$–tilted convex" is membership in the published class `classF γ`. $\operatorname{lsc}(f|_{\operatorname{ri}(K)})$ is `lscEnv (ri K) f`, the envelope of $f$ on $\operatorname{ri}(K)$ extended by $+\infty$.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: lsc(f|ri(K)) → lscEnv (intrinsicInterior ℝ K) f; reason: the paper's envelope of f on ri(K), +∞ elsewhere (§3, p.10)
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 10, p.21

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_classF
import Definitions.Def_TiltedCvx_Supplement_lscEnv

namespace TiltedCvx.Supplement

/-- **Theorem 10 (values on the relative interior determine the function).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 10, p.21. Let `γ ∈ (0, 1]`, and let
`f, g : ℝ^d → ℝ̄` be proper, lsc, and γ–tilted convex. Set `K := dom(f)`. If `f = g` on `ri(K)`,
then `f = g` on the closure `K̄`. Moreover, `f = lsc(f|ri(K))`.

**Formalization Note** "Proper, lsc, and γ–tilted convex" is membership in the published
`classF γ`. `ri(K)` is `intrinsicInterior ℝ K` and `K̄` is `closure K` (the bar is lost in the
text layer; the rendered page has `K̄`). `lsc(f|ri(K))` is `lscEnv (ri K) f`: the lsc envelope of
`f` on `ri(K)`, `+∞` elsewhere. The "Moreover" equality is of functions on all of `ℝ^d`. -/
theorem theorem_10 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f g : E → EReal)
    (hf : f ∈ (TiltedCvx.classF γ : Set (E → EReal)))
    (hg : g ∈ (TiltedCvx.classF γ : Set (E → EReal))) :
    (Set.EqOn f g (intrinsicInterior ℝ (TiltedCvx.effDom f)) →
      Set.EqOn f g (closure (TiltedCvx.effDom f))) ∧
    f = lscEnv (intrinsicInterior ℝ (TiltedCvx.effDom f)) f := by sorry

end TiltedCvx.Supplement
