-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_18
-- name    : TiltedCvx.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:33:14.961422+00:00
-- url     : https://prove2.me/theorems/d1b8ff07-80d3-4dd6-bd6b-4da2e5ae8ce8
-- title:
--   Theorem 18 — Jensen form of tilted secant convexity
-- statement:
--   Let $\gamma\in[0,1]$ and $f:K\to\mathbb R\cup\{+\infty\}$. Then $f$ is $\gamma$–tilted secant convex if and only if
--
--   $$
--   f(\lambda y+(1-\lambda)z)\ \le\ M_{\gamma,\lambda}\big(f(y),f(z)\big)\qquad\text{for all }y,z\in\operatorname{dom}(f),\ \lambda\in[0,1],\qquad\text{(16)}
--   $$
--
--   where $M_{\gamma,\lambda}$ is the binary tilted mean (14)–(15) ($M_{0,\lambda}=\max$, $M_{1,\lambda}$ the arithmetic mean).
--
--   This weakens Jensen's inequality by down-weighting the smaller endpoint value by $\gamma$; at $\gamma=1$ it is convexity, at $\gamma=0$ quasiconvexity.
--
--   **Formalization Note** $f$ is encoded by its proper extension, a function $E\to\overline{\mathbb R}$ that never takes $-\infty$.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: f : K → ℝ ∪ {+∞} on a convex K → f : E → EReal with f x ≠ ⊥ for all x (its proper extension); reason: both sides read f only on dom f; every such function is the extension of itself on K = E, and conversely
--   - encoding: M_{γ,λ}(a, b) of (14)–(15) → binMean γ λ a b on the real values f(y), f(z); reason: the paper's formula, including the γ = 0 convention
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 18, p.25

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_TiltedSecant
import Definitions.Def_TiltedCvx_Supplement_binMean

namespace TiltedCvx.Supplement

/-- **Theorem 18 (Jensen form).** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 18,
p.25. Let `γ ∈ [0, 1]` and `f : K → ℝ ∪ {+∞}`. Then `f` is γ–tilted secant convex if and only if
`f(λy + (1 − λ)z) ≤ M_{γ,λ}(f(y), f(z))` for all `y, z ∈ dom(f)` and `λ ∈ [0, 1]` (16).

**Formalization Note** `f : K → ℝ ∪ {+∞}` (with `K` the convex set of §4) is encoded by its
proper extension, a function `E → EReal` that never takes `−∞` (`+∞` off `K`); only `dom f`
enters both sides. `M_{γ,λ}` is `binMean`, with the `γ = 0` convention (15); its arguments are the
real values `f(y), f(z)`. -/
theorem theorem_18 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hbot : ∀ x, f x ≠ ⊥) :
    TiltedCvx.TiltedSecant γ f ↔
      ∀ y ∈ TiltedCvx.effDom f, ∀ z ∈ TiltedCvx.effDom f, ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
        f (l • y + (1 - l) • z) ≤ ((binMean γ l (f y).toReal (f z).toReal : ℝ) : EReal) := by sorry

end TiltedCvx.Supplement
