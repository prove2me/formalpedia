-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_5
-- name    : TiltedCvx.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:28:18.590448+00:00
-- url     : https://prove2.me/theorems/b978044c-334d-4e3a-b78f-302e92f91ba0
-- title:
--   Theorem 5 — minimizers of γ–tilted convex functions
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper, lower semicontinuous and $\gamma$–tilted convex for some $\gamma\in(0,1]$. For every $x\in\operatorname{dom}(f)$ the following are equivalent:
--
--   1. $x$ is a global minimizer of $f$;
--   2. $x$ is a local minimizer of $f$;
--   3. $0\in\hat\partial f(x)$ (Fréchet subdifferential);
--   4. $0\in\overline\partial f(x)$ (Clarke–Rockafellar subdifferential).
--
--   As for convex functions, local minimizers are global, and stationarity in either subdifferential characterizes them.
--
--   **Formalization Note** $\hat\partial f$ and $\overline\partial f$ are the published `frechetSubdiff` and `ClarkeSubdiff`.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: global / local minimizer → IsMinOn f Set.univ x / IsLocalMin f x in the order of EReal; reason: the standard definitions
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 5, p.18

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedConvex
import Definitions.Def_ClarkeStrat_Proj_Setting
import Definitions.Def_NAPPAL_VPEB_frechetSubdiff

open ClarkeStrat.Proj NAPPAL.VPEB

namespace TiltedCvx.Supplement

/-- **Theorem 5 (minimizers).** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 5,
p.18. Let `f : ℝ^d → ℝ̄` be proper, lsc, and γ–tilted convex for some `γ ∈ (0, 1]`. Then, for
every `x ∈ dom(f)`, the following are equivalent:
(i) `x` is a global minimizer of `f`;
(ii) `x` is a local minimizer of `f`;
(iii) `0 ∈ ∂̂f(x)`;
(iv) `0 ∈ ∂̄f(x)`.

**Formalization Note** A global minimizer is `IsMinOn f Set.univ x` (`f x ≤ f y` for all `y`), a
local minimizer `IsLocalMin f x`, both for the `EReal` order. `∂̂f` is the published
`NAPPAL.VPEB.frechetSubdiff`, `∂̄f` the published `ClarkeStrat.Proj.ClarkeSubdiff`. -/
theorem theorem_5 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hf : TiltedCvx.IsProper f) (hlsc : LowerSemicontinuous f)
    (htc : TiltedCvx.TiltedConvex γ f) (x : E) (hx : x ∈ TiltedCvx.effDom f) :
    List.TFAE
      [IsMinOn f Set.univ x,
       IsLocalMin f x,
       (0 : E) ∈ frechetSubdiff f x,
       (0 : E) ∈ ClarkeSubdiff f x] := by sorry

end TiltedCvx.Supplement
