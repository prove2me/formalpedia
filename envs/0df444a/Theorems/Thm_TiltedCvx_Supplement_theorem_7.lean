-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_7
-- name    : TiltedCvx.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:29:09.125522+00:00
-- url     : https://prove2.me/theorems/df295e3c-047d-468c-9106-c742044d717e
-- title:
--   Theorem 7 — continuity on the domain in dimension one
-- statement:
--   Let $f:\mathbb R\to\overline{\mathbb R}$ be proper, lower semicontinuous and $\gamma$–tilted convex for some $\gamma\in(0,1]$, and set $K:=\operatorname{dom}(f)$. Then
--
--   $$
--   f|_K\ \text{is continuous.}
--   $$
--
--   Combined with the line criterion (Theorem 9) this shows that every proper lsc $\gamma$–tilted convex function on $\mathbb R^d$ is radially continuous (Corollary 2).
--
--   Differences from the source:
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: f|K is continuous → ContinuousOn f K for the EReal-valued f; reason: f is finite on K and the order topology of EReal restricts to that of ℝ
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 7, p.19

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedConvex

namespace TiltedCvx.Supplement

/-- **Theorem 7 (continuity on the domain in dimension one).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorem 7, p.19. Let `f : ℝ → ℝ̄` be proper, lsc, and γ–tilted convex for some
`γ ∈ (0, 1]`, and set `K := dom(f)`. Then `f|K` is continuous.

**Formalization Note** `ℝ` carries its standard inner product; "`f|K` is continuous" is
`ContinuousOn f K` for the `EReal`-valued `f` (on `K` it is finite). -/
theorem theorem_7 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : ℝ → EReal)
    (hf : TiltedCvx.IsProper f) (hlsc : LowerSemicontinuous f)
    (htc : TiltedCvx.TiltedConvex γ f) :
    ContinuousOn f (TiltedCvx.effDom f) := by sorry

end TiltedCvx.Supplement
