-- Prove2me | Theorems.Thm_TiltedCvx_theorem_16
-- name    : TiltedCvx.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:41:16.523266+00:00
-- url     : https://prove2.me/theorems/be30693b-a2c7-424b-b933-cb4f3022864f
-- title:
--   Theorem 16 — line restrictions of $\gamma$-tilted monotone subdifferentials
-- statement:
--   Let $\gamma\in(0,1]$ and let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper and lower semicontinuous. Then $\bar\partial f$ is $\gamma$–tilted monotone if and only if, for every line $\ell$ meeting $\operatorname{dom}(f)$, the operator
--
--   $$
--   \bar\partial\big(f|_\ell\big)
--   $$
--
--   is $\gamma$–tilted monotone on $\ell$. Moreover, when these equivalent conditions hold, the same conclusion is true for the restriction of $f$ (extended by $+\infty$) to any nonempty closed interval contained in $\ell$ and meeting $\operatorname{dom}(f)$.
--
--   **Formalization Note** A line is $\{x+te\}$ with $\|e\|=1$, identified with $\mathbb R$ by $t\mapsto x+te$; the restriction to a set $I$ of parameters is `lineRestrict f x e I`. A closed interval of $\mathbb R$ (a point, a bounded interval, a half-line or $\mathbb R$) is a closed order-connected set.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: line ℓ regarded as a one-dimensional Euclidean space → ℝ via t ↦ x + t e, ‖e‖ = 1; reason: an isometry onto ℓ
--   - encoding: nonempty closed interval contained in ℓ → closed order-connected I ⊆ ℝ of parameters, meeting dom f; reason: the closed intervals of ℝ are exactly the closed order-connected sets; nonempty follows from meeting dom f
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 16, p.24

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedMonotone
import Definitions.Def_TiltedCvx_lineRestrict
import Definitions.Def_ClarkeStrat_Proj_Setting

open ClarkeStrat.Proj

namespace TiltedCvx

/-- **Theorem 16 (line restrictions of γ–tilted monotone subdifferentials).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 16, p.24. Let `γ ∈ (0, 1]` and let
`f : ℝ^d → ℝ̄` be proper lsc. Then `∂̄f` is γ–tilted monotone if and only if, for every line `ℓ`
meeting `dom(f)`, the operator `∂̄(f|ℓ)` is γ–tilted monotone on `ℓ`. Moreover, when these
equivalent conditions hold, the same conclusion is true for the restriction of `f` to any
nonempty closed interval contained in `ℓ` and meeting `dom(f)`.

**Formalization Note** A line is `{x + t e : t ∈ ℝ}` with `‖e‖ = 1`, identified with `ℝ` by the
isometry `t ↦ x + t e`; the restriction to an interval `I ⊆ ℝ` of parameters is extended by `+∞`
(p.24: "extended by +∞ outside its effective domain"), i.e. `lineRestrict f x e I`. A closed
interval of `ℝ` (possibly a point or unbounded) is a closed order-connected set. -/
theorem theorem_16 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    (TiltedMonotone γ (ClarkeSubdiff f) ↔
      ∀ x e : E, ‖e‖ = 1 → (∃ t : ℝ, x + t • e ∈ effDom f) →
        TiltedMonotone γ (ClarkeSubdiff (lineRestrict f x e Set.univ))) ∧
    (TiltedMonotone γ (ClarkeSubdiff f) →
      ∀ x e : E, ‖e‖ = 1 → ∀ I : Set ℝ, IsClosed I → I.OrdConnected →
        (∃ t ∈ I, x + t • e ∈ effDom f) →
        TiltedMonotone γ (ClarkeSubdiff (lineRestrict f x e I))) := by sorry

end TiltedCvx
