-- Prove2me | Theorems.Thm_TiltedCvx_theorem_21
-- name    : TiltedCvx.theorem_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:29.258208+00:00
-- url     : https://prove2.me/theorems/fd1e8d09-a0fb-4018-8ef7-55bf1213e840
-- title:
--   Theorem 21 — secant convexity lies between tilted monotonicity and tilted convexity
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper and lower semicontinuous and $\gamma\in(0,1]$.
--
--   1. If $f$ is $\gamma$–tilted secant convex, then $f$ is $\gamma$–tilted convex.
--   2. If $\bar\partial f$ is $\gamma$–tilted monotone, then $f$ is $\gamma$–tilted secant convex.
--
--   In particular, for every proper lsc $f$,
--
--   $$
--   \gamma^*_{\mathrm{mono}}(f)\ \le\ \gamma^*_{\mathrm{sec}}(f)\ \le\ \gamma^*(f).
--   $$
--
--   These are the two middle inclusions $\mathcal F^\gamma_{\mathrm{mono}}\subseteq\mathcal F^\gamma_{\mathrm{sec}}\subseteq\mathcal F^\gamma$ of the main chain.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: sup{γ ∈ [0,1] : …} with sup ∅ := 0 → real sSup of a subset of [0,1]; reason: the set is bounded by 1 and Mathlib's sSup ∅ = 0 is the paper's convention; same value
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 21, p.27

import Mathlib
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedConvex
import Definitions.Def_TiltedCvx_TiltedMonotone
import Definitions.Def_TiltedCvx_TiltedSecant
import Definitions.Def_TiltedCvx_gammaStar
import Definitions.Def_TiltedCvx_gammaMono
import Definitions.Def_TiltedCvx_gammaSec
import Definitions.Def_ClarkeStrat_Proj_Setting

open ClarkeStrat.Proj

namespace TiltedCvx

/-- **Theorem 21 (secant convexity lies between the other two notions).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 21, p.27. Let `f : ℝ^d → ℝ̄` be proper
lsc and `γ ∈ (0, 1]`.
(i) If `f` is γ–tilted secant convex, then `f` is γ–tilted convex.
(ii) If `∂̄f` is γ–tilted monotone, then `f` is γ–tilted secant convex.
In particular, `γ*_mono(f) ≤ γ*_sec(f) ≤ γ*(f)`.

**Formalization Note** The "in particular" bounds hold for every proper lsc `f` and are stated
outside the quantifier over `γ`. -/
theorem theorem_21 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    (∀ γ : ℝ, 0 < γ → γ ≤ 1 →
      (TiltedSecant γ f → TiltedConvex γ f) ∧
      (TiltedMonotone γ (ClarkeSubdiff f) → TiltedSecant γ f)) ∧
    gammaMono f ≤ gammaSec f ∧ gammaSec f ≤ gammaStar f := by sorry

end TiltedCvx
