-- Prove2me | Theorems.Thm_TiltedCvx_theorem_14
-- name    : TiltedCvx.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:32.757787+00:00
-- url     : https://prove2.me/theorems/7efb869b-a72c-426d-a2fb-cbdcdb205122
-- title:
--   Theorem 14 — tilted monotone ⇒ tilted convex ⇒ $\gamma^2$-tilted monotone
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper and lower semicontinuous, let $F:\mathbb R^d\rightrightarrows\mathbb R^d$ be an operator with $\operatorname{dom}(F)\subseteq\operatorname{dom}(f)$, and let $\gamma\in(0,1]$.
--
--   1. If $\hat\partial f$ is $\gamma$–tilted monotone, then $f$ is $\gamma$–tilted convex.
--   2. If $f$ is $\gamma$–tilted convex with respect to $F$, then $F$ is $\gamma^2$–tilted monotone.
--
--   In particular, for every proper lsc $f$,
--
--   $$
--   \gamma^*_{\mathrm{mono}}(f)\ \le\ \gamma^*(f)\ \le\ \big(\gamma^*_{\mathrm{mono}}(f)\big)^{1/2}.
--   $$
--
--   **Formalization Note** $\operatorname{dom}(F)$ is the set of points where $F$ is nonempty. The "in particular" bounds are stated for $f$ alone, outside the quantifiers over $\gamma$ and $F$.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: sup{γ ∈ [0,1] : …} with sup ∅ := 0 → real sSup of a subset of [0,1]; reason: the set is bounded by 1 and Mathlib's sSup ∅ = 0 is the paper's convention; same value
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 14, p.23

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_NAPPAL_VPEB_frechetSubdiff
import Definitions.Def_TiltedCvx_TiltedConvexWrt
import Definitions.Def_TiltedCvx_TiltedConvex
import Definitions.Def_TiltedCvx_TiltedMonotone
import Definitions.Def_TiltedCvx_gammaStar
import Definitions.Def_TiltedCvx_gammaMono

open NAPPAL.VPEB

namespace TiltedCvx

/-- **Theorem 14 (tilted monotone ⇒ tilted convex ⇒ squared tilted monotone).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 14, p.23. Let `f : ℝ^d → ℝ̄` be proper
lsc, `F : ℝ^d ⇒ ℝ^d` with `dom(F) ⊆ dom(f)`, and `γ ∈ (0, 1]`.
(i) If `∂̂f` is γ–tilted monotone, then `f` is γ–tilted convex.
(ii) If `f` is γ–tilted convex with respect to `F`, then `F` is γ²–tilted monotone.
In particular, `γ*_mono(f) ≤ γ*(f) ≤ (γ*_mono(f))^{1/2}`.

**Formalization Note** `∂̂f` is the published `NAPPAL.VPEB.frechetSubdiff`; `dom(F) = {x | F x ≠ ∅}`. The "in particular" bounds hold for every proper
lsc `f`, so they are stated outside the quantifier over `γ` and `F`. -/
theorem theorem_14 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    (∀ F : E → Set E, (∀ x, (F x).Nonempty → x ∈ effDom f) →
      ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
        (TiltedMonotone γ (frechetSubdiff f) → TiltedConvex γ f) ∧
        (TiltedConvexWrt γ f F → TiltedMonotone (γ ^ 2) F)) ∧
    gammaMono f ≤ gammaStar f ∧ gammaStar f ≤ Real.sqrt (gammaMono f) := by sorry

end TiltedCvx
