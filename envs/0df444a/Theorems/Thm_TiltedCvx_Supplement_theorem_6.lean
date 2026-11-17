-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_6
-- name    : TiltedCvx.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:28:46.546606+00:00
-- url     : https://prove2.me/theorems/6785e2ff-bad6-4b70-a91e-c0a7b98b3f10
-- title:
--   Theorem 6 — local Lipschitz continuity on $\operatorname{ri}(\operatorname{dom} f)$
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper, lower semicontinuous and $\gamma$–tilted convex for some $\gamma\in(0,1]$, and set $K:=\operatorname{dom}(f)$. Then
--
--   $$
--   f|_{\operatorname{ri}(K)}\ \text{is locally Lipschitz.}
--   $$
--
--   Like convex functions, tilted convex functions are locally Lipschitz on the relative interior of their domain (they need not be at the boundary: $-\sqrt x$ on $[0,1]$).
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: f|ri(K) is locally Lipschitz → LocallyLipschitzOn (ri K) of x ↦ (f x).toReal, ri K = intrinsicInterior ℝ K; reason: f is finite on ri(K) ⊆ dom f, so toReal reads its values; same condition
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 6, p.19

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedConvex

namespace TiltedCvx.Supplement

/-- **Theorem 6 (local Lipschitz continuity on the relative interior).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 6, p.19. Let `f : ℝ^d → ℝ̄` be
proper, lsc, and γ–tilted convex for some `γ ∈ (0, 1]`, and set `K := dom(f)`. Then `f|ri(K)` is
locally Lipschitz.

**Formalization Note** `ri(K)` is `intrinsicInterior ℝ K`. "`f|ri(K)` is locally Lipschitz" is
Mathlib's `LocallyLipschitzOn (ri K)` for the real function `x ↦ (f x).toReal`: every
`x ∈ ri(K)` has a neighbourhood within `ri(K)` on which it is Lipschitz. Since
`ri(K) ⊆ K = dom f`, `f` is finite there and `toReal` reads the true values. -/
theorem theorem_6 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hf : TiltedCvx.IsProper f) (hlsc : LowerSemicontinuous f)
    (htc : TiltedCvx.TiltedConvex γ f) :
    LocallyLipschitzOn (intrinsicInterior ℝ (TiltedCvx.effDom f))
      (fun x => (f x).toReal) := by sorry

end TiltedCvx.Supplement
