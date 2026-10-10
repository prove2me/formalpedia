-- Prove2me | Theorems.Thm_QuasiHemiVI_Existence_theorem_3_4_iii
-- name    : QuasiHemiVI.Existence.theorem_3_4_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:36:33.403532+00:00
-- url     : https://prove2.me/theorems/3c5b5fb1-5d0c-47df-a0a5-42570c8377e1
-- title:
--   Theorem 3.4 (iii) — for convex $h$, $\mathrm{SOL}(C;T,J,\varphi,f)$ is convex
-- statement:
--   Let $V$ be a real reflexive Banach space and $X$, $Y$ real Banach spaces. Assume (HC), (HJ), (Hγ), (H0), (HT), (Hφ) and the coercivity condition (3.2) (with a bounded set $C_0$ meeting $C$). If, in addition, the function $h:V\to\mathbb R$ of (HT)(ii) is convex, then
--
--   $$
--   \mathrm{SOL}(C;T,J,\varphi,f)\ \text{is a convex subset of } V.
--   $$
--
--   Convexity of the values of the variational selection $S$ is one of the hypotheses of Kluge's fixed point theorem in the proof of Theorem 3.8.
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, p. 1251, Theorem 3.4 (iii)

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_QuasiHemiVI_Existence_SetValued
import Definitions.Def_QuasiHemiVI_Existence_Hypotheses
import Definitions.Def_QuasiHemiVI_Existence_Problems

namespace QuasiHemiVI.Existence

/-- Theorem 3.4 (iii), p. 1251: under (HC), (HJ), (Hγ), (H0), (HT), (Hφ) and (3.2), if in addition
`h` is convex, then `SOL(C; T, J, φ, f)` is convex in `V`. -/
theorem theorem_3_4_iii {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (hV : IsReflexive V)
    (C : Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (π : V →L[ℝ] Y) (f : Y →L[ℝ] ℝ) (h : V → ℝ) (C₀ : Set V)
    (hC : HC C) (hJ : LocallyLipschitz J) (hT : HT C T φ J γ π f h) (hφ : Hphi φ)
    (h32 : Coercive32 C T φ J γ C₀)
    (hhcvx : ConvexOn ℝ Set.univ h) :
    Convex ℝ (SOL C T φ J γ π f) := by sorry

end QuasiHemiVI.Existence
