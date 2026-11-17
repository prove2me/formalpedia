-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_3
-- name    : TiltedCvx.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:27:37.001521+00:00
-- url     : https://prove2.me/theorems/73882b2d-6a63-42cc-9217-5626f032899f
-- title:
--   Theorem 3 — pseudoconvexity through the Clarke subdifferential
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper, lower semicontinuous and radially continuous. The following are equivalent:
--
--   1. for all $x,y\in\operatorname{dom}(f)$ and $v\in\overline\partial f(x)$ with $\langle y-x,v\rangle\ge0$, $\ f(y)\ge f(x)$;
--   2. $f$ is $0^+$–tilted convex;
--   3. $f$ is pseudoconvex (Definition 10);
--   4. the operator $\overline\partial f$ is $0^+$–tilted monotone;
--   5. the operator $\overline\partial f$ is pseudomonotone.
--
--   With $\psi_{0^+}(z)=0$ for $z\ge0$ and $-\infty$ for $z<0$, the endpoint $0^+$ of the tilted scale is pseudoconvexity, whereas $0$ is quasiconvexity (Theorem 2).
--
--   **Formalization Note** Pseudoconvexity is the general Definition 10 with the Clarke subdifferential, so items 1 and 3 coincide by definition, as in the paper's proof.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: pseudoconvexity of a proper lsc radially continuous f (Definition 10) → IsPseudoconvex f, whose predicate omits the standing hypotheses; the theorem carries them; reason: the theorem assumes exactly those hypotheses, so the predicate is the paper's on every f it is applied to
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 3, p.17

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_ClarkeStrat_Proj_Setting
import Definitions.Def_TiltedCvx_Supplement_RadiallyContinuous
import Definitions.Def_TiltedCvx_Supplement_IsPseudoconvex
import Definitions.Def_TiltedCvx_Supplement_IsPseudomonotone
import Definitions.Def_TiltedCvx_Supplement_TiltedConvexZeroPlus
import Definitions.Def_TiltedCvx_Supplement_TiltedMonotoneZeroPlus

open scoped InnerProductSpace
open ClarkeStrat.Proj

namespace TiltedCvx.Supplement

/-- **Theorem 3 (pseudoconvexity through the Clarke subdifferential).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 3, p.17. Let `f : ℝ^d → ℝ̄` be a
proper, lsc, and radially continuous function. Then the following are equivalent:
(i) for all `x, y ∈ dom(f)` and `v ∈ ∂̄f(x)` such that `⟨y − x, v⟩ ≥ 0`, `f(y) ≥ f(x)`;
(ii) `f` is 0⁺–tilted convex;
(iii) `f` is pseudoconvex;
(iv) the operator `∂̄f` is 0⁺–tilted monotone;
(v) the operator `∂̄f` is pseudomonotone.

**Formalization Note** Pseudoconvexity is the general Definition 10 (with the Clarke `∂̄f`), so
(i) and (iii) coincide by definition, as the paper's proof notes. -/
theorem theorem_3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) (hf : TiltedCvx.IsProper f)
    (hlsc : LowerSemicontinuous f) (hrad : RadiallyContinuous f) :
    List.TFAE
      [∀ x ∈ TiltedCvx.effDom f, ∀ y ∈ TiltedCvx.effDom f, ∀ v ∈ ClarkeSubdiff f x,
          0 ≤ ⟪y - x, v⟫_ℝ → f x ≤ f y,
       TiltedConvexZeroPlus f,
       IsPseudoconvex f,
       TiltedMonotoneZeroPlus (ClarkeSubdiff f),
       IsPseudomonotone (ClarkeSubdiff f)] := by sorry

end TiltedCvx.Supplement
