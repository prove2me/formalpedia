-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_36
-- name    : TiltedCvx.Supplement.theorem_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:37:31.225084+00:00
-- url     : https://prove2.me/theorems/fb55bdc3-f013-4d16-b0a6-c2c4250880e7
-- title:
--   Theorem 36 — continuity along lines through $\operatorname{ri}(K)$
-- statement:
--   Let $\gamma\in(0,1]$, $f:\mathbb R^d\to\overline{\mathbb R}$ proper and lower semicontinuous, $K:=\operatorname{dom}(f)$ convex, and $F:\mathbb R^d\rightrightarrows\mathbb R^d$ such that $K\cap\operatorname{dom}(F)$ is dense in $K$ and $f$ is approximately $\gamma$–tilted convex with respect to $F$. Then for every line $\ell$ that intersects $\operatorname{ri}(K)$,
--
--   $$
--   f|_{\ell\cap K}\ \text{is continuous.}
--   $$
--
--   Approximate supports on a dense set thus already give continuity along every line through the relative interior, including at the endpoints of $\ell\cap K$.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: K ∩ dom(F) dense in K → K ⊆ closure (K ∩ {x | F x ≠ ∅}); reason: the meaning of density in K
--   - encoding: a line ℓ meeting ri(K); f|ℓ∩K continuous → ℓ = range (t ↦ p + t • e), e ≠ 0, with some p + t • e ∈ ri K; ContinuousOn f (ℓ ∩ K) in EReal; reason: f is finite on K and the order topology of EReal restricts to that of ℝ
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 36, p.58

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_Supplement_ApproxTiltedConvexWrt

namespace TiltedCvx.Supplement

/-- **Theorem 36 (continuity along lines).** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Theorem 36, p.58. Let `γ ∈ (0, 1]`, let `f : ℝ^d → ℝ̄` be proper and lsc, and set `K := dom(f)`.
Assume that `K` is convex. Let `F : ℝ^d ⇒ ℝ^d` be such that `K ∩ dom(F)` is dense in `K`, and
suppose that `f` is approximately γ–tilted convex with respect to `F` (Definition 16). Then, for
every line `ℓ` that intersects `ri(K)`, the restriction `f|ℓ∩K` is continuous.

**Formalization Note** A line is `ℓ = {p + t e : t ∈ ℝ}` with `e ≠ 0`; it intersects `ri(K)` when
some `p + t e ∈ intrinsicInterior ℝ K`. "`f|ℓ∩K` is continuous" is `ContinuousOn f (ℓ ∩ K)` for the
`EReal`-valued `f` (finite on `K`). Density is `K ⊆ closure (K ∩ {x | F x ≠ ∅})`. -/
theorem theorem_36 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hf : TiltedCvx.IsProper f) (hlsc : LowerSemicontinuous f)
    (hK : Convex ℝ (TiltedCvx.effDom f)) (F : E → Set E)
    (hdense : TiltedCvx.effDom f ⊆ closure (TiltedCvx.effDom f ∩ {x | (F x).Nonempty}))
    (happrox : ApproxTiltedConvexWrt γ f F) :
    ∀ p e : E, e ≠ 0 →
      (∃ t : ℝ, p + t • e ∈ intrinsicInterior ℝ (TiltedCvx.effDom f)) →
      ContinuousOn f (Set.range (fun t : ℝ => p + t • e) ∩ TiltedCvx.effDom f) := by sorry

end TiltedCvx.Supplement
