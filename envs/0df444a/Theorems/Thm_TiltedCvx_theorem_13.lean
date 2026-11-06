-- Prove2me | Theorems.Thm_TiltedCvx_theorem_13
-- name    : TiltedCvx.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:21.838995+00:00
-- url     : https://prove2.me/theorems/9ed7d02f-a790-4043-921e-640a477c01f7
-- title:
--   Theorem 13 — the extremal profile $\vartheta_\gamma$ and power interpolation
-- statement:
--   Let $\gamma\in(0,1]$ and let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper, lower semicontinuous and $\gamma$–tilted convex, with $K:=\operatorname{dom}(f)$. Let
--
--   $$
--   \vartheta_\gamma(s):=\min\{s^\gamma,\ 1-(1-s)^{1/\gamma}\}\quad(s\in[0,1]),\qquad\vartheta_\gamma(s)=+\infty\quad(s\notin[0,1]).
--   $$
--
--   Then:
--
--   1. $\vartheta_\gamma$ is $\gamma$–tilted convex.
--   2. Every proper lsc $\gamma$–tilted convex $g:\mathbb R\to\overline{\mathbb R}$ with $g(0)=0$ and $g(1)=1$ satisfies $g(s)\le\vartheta_\gamma(s)$.
--   3. For $y,z\in K$, $t\in[0,1]$ and $x:=(1-t)y+tz$,
--   $$
--   f(x)\le\begin{cases} f(y)+\big(f(z)-f(y)\big)\vartheta_\gamma(t), & f(y)\le f(z),\\ f(z)+\big(f(y)-f(z)\big)\vartheta_\gamma(1-t), & f(y)\ge f(z).\end{cases}
--   $$
--   4. For the same $x,y,z,t$, $\ f(x)\le(1-\gamma)\max\{f(y),f(z)\}+\gamma\big((1-t)f(y)+tf(z)\big)$.
--
--   The bound in 3 is the sharp interpolation inequality of the class; 4 shows that tilted convexity lies between convexity and quasiconvexity.
--
--   **Formalization Note** Definition 3 defines tilted convexity only for proper lsc functions, so item 1 is stated as $\vartheta_\gamma\in\mathcal F^\gamma$ on $\mathbb R$. In items 3–4 the values at $y,z$ are real.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - reading: (i) ϑγ is γ–tilted convex → ϑγ ∈ F^γ (proper, lsc and γ–tilted convex); reason: Definition 3 defines γ–tilted convexity only for proper lsc functions, so the assertion presupposes both
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 13, p.22

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedConvex
import Definitions.Def_TiltedCvx_classF
import Definitions.Def_TiltedCvx_thetaProfile
import Definitions.Def_TiltedCvx_theta

namespace TiltedCvx

/-- **Theorem 13 (power interpolation along segments).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorem 13, p.22. Let `γ ∈ (0, 1]` and let `f : ℝ^d → ℝ̄` be proper, lsc and
γ–tilted convex, with `K := dom(f)`. Let `ϑγ(s) := min{s^γ, 1 − (1 − s)^{1/γ}}` on `[0, 1]` and
`+∞` elsewhere (11). Then:
(i) `ϑγ` is γ–tilted convex;
(ii) every proper lsc γ–tilted convex `g : ℝ → ℝ̄` with `g(0) = 0`, `g(1) = 1` satisfies
`g(s) ≤ ϑγ(s)`;
(iii) for `y, z ∈ K`, `t ∈ [0, 1]` and `x := (1 − t)y + tz`,
`f(x) ≤ f(y) + (f(z) − f(y)) ϑγ(t)` if `f(y) ≤ f(z)`, and
`f(x) ≤ f(z) + (f(y) − f(z)) ϑγ(1 − t)` if `f(y) ≥ f(z)` (12);
(iv) `f(x) ≤ (1 − γ) max{f(y), f(z)} + γ((1 − t)f(y) + tf(z))` (13).

**Formalization Note** Definition 3 defines γ–tilted convexity only for proper lsc functions, so
(i) is stated as `ϑγ ∈ F^γ` (on `ℝ`). In (iii) and (iv) the values at `y, z ∈ K` are real, and
`ϑγ(t)` for `t ∈ [0, 1]` is the real formula `thetaProfile γ t`. -/
theorem theorem_13 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hf : IsProper f) (hlsc : LowerSemicontinuous f) (htc : TiltedConvex γ f) :
    theta γ ∈ (classF γ : Set (ℝ → EReal)) ∧
    (∀ g : ℝ → EReal, IsProper g → LowerSemicontinuous g → TiltedConvex γ g →
      g 0 = 0 → g 1 = 1 → ∀ s : ℝ, g s ≤ theta γ s) ∧
    (∀ y ∈ effDom f, ∀ z ∈ effDom f, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (f y ≤ f z → f ((1 - t) • y + t • z) ≤
        (((f y).toReal + ((f z).toReal - (f y).toReal) * thetaProfile γ t : ℝ) : EReal)) ∧
      (f z ≤ f y → f ((1 - t) • y + t • z) ≤
        (((f z).toReal + ((f y).toReal - (f z).toReal) * thetaProfile γ (1 - t) : ℝ) : EReal))) ∧
    (∀ y ∈ effDom f, ∀ z ∈ effDom f, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f ((1 - t) • y + t • z) ≤
        (((1 - γ) * max (f y).toReal (f z).toReal +
          γ * ((1 - t) * (f y).toReal + t * (f z).toReal) : ℝ) : EReal)) := by sorry

end TiltedCvx
