-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_theorem_7_1
-- name    : SelfScaledIPM.FuncProx.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:13.626311+00:00
-- url     : https://prove2.me/theorems/e21f7d6a-17b4-4591-9e1a-78daf53ba628
-- title:
--   Theorem 7.1, p. 32 — Algorithm 7.1: gap × (1 − α), α²/(1 − α) ≥ ω₁(Δ, κ)/ν, (7.3), and N ≤ ⌈Δ/(τ̄ − ln(1 + τ̄))⌉ Newton corrections
-- statement:
--   Fix $\Delta>0$ and $\kappa\in(0,1)$, and let $\beta=\kappa-\ln(1+\kappa)$. There are constants $\omega_1=\omega_1(\Delta,\kappa)>0$ and $\omega_2=\omega_2(\Delta,\kappa)>0$, depending on $\Delta$ and $\kappa$ only, such that the following holds for every proper cone $K\subseteq\mathbb R^n$ with a $\nu$-self-scaled barrier $F$ and every primal-dual conic problem with data $(A,b,c)$, $A$ surjective.
--
--   Consider one iteration of Algorithm 7.1 (predictor-corrector method II) from a point $(x,y,s)\in\mathcal F(\beta)$, i.e. strictly feasible with $\gamma_F(x,s)\le\beta$:
--
--   1. let $w$ be the scaling point of $(x,s)$ and $(p_x,p_y,p_s)$ the affine-scaling direction;
--   2. let $\alpha$ be the largest step in $[0,1)$ such that $x-\alpha'p_x\in\operatorname{int}K$ and $s-\alpha'p_s\in\operatorname{int}K^*$ for all $\alpha'\in[0,\alpha]$ and $\gamma_F(x-\alpha p_x,s-\alpha p_s)=\beta+\Delta$;
--   3. run the Newton process (5.25) from $(x-\alpha p_x,\,y-\alpha p_y,\,s-\alpha p_s)$, obtaining $z_0,z_1,z_2,\dots$
--
--   Then
--   $$\frac{\alpha^2}{1-\alpha}\ge\frac1\nu\,\omega_1, \tag{7.2}$$
--   $$\frac{\alpha^2}{1-\alpha}\ge\frac{\omega_2}{|p_x|_x\cdot\|p_s\|_s}\ge\frac{\omega_2}{\sqrt\nu\,|p_x|_x\cdot|p_s|_s}, \tag{7.3}$$
--   and the Newton process reaches $\mathcal F(\beta)$: the first index $N$ with $z_N\in\mathcal F(\beta)$ exists and satisfies
--   $$N\le\Big\lceil\frac{\Delta}{\bar\tau-\ln(1+\bar\tau)}\Big\rceil,\qquad\bar\tau=\frac12\sqrt{\frac{3\beta}{1+\beta}}, \tag{7.4}$$
--   and the new iterate $z_N=(x_+,y_+,s_+)$ satisfies
--   $$\langle s_+,x_+\rangle\le(1-\alpha)\langle s,x\rangle. \tag{7.1}$$
--
--   Thus the method reduces the duality gap at a linear rate with factor $1-\Omega(1/\sqrt\nu)$, using a bounded number of corrector steps per iteration, while the neighbourhood $\mathcal F(\beta+\Delta)$ of the predictor can be arbitrarily wide.
--
--   **Formalization Note** The constants $\omega_1,\omega_2$ are quantified before the cone, barrier, problem and iterate, so they are uniform in all of them. "The largest stepsize" is `IsGreatest` over steps whose whole segment $[0,\alpha]$ stays strictly feasible (by convexity of the interiors this is the same as the endpoint being strictly feasible). Algorithm 7.1 prints the predictor point as $(x-\alpha p_x,x-\alpha p_x,x-\alpha p_x)$, a misprint for $(x-\alpha p_x,y-\alpha p_y,s-\alpha p_s)$, which is used here. The printed (7.4) reads $N_k\le\Delta/(\bar\tau-\ln(1+\bar\tau))$; it is stated with the ceiling, because $N\ge1$ always (the predictor point lies outside $\mathcal F(\beta)$) while $\Delta/(\bar\tau-\ln(1+\bar\tau))$ can be smaller than $1$. In Lean a quotient with zero denominator is $0$, so the first part of (7.3) is trivially true if $|p_x|_x\|p_s\|_s=0$; that case cannot occur under the hypotheses. Points are triples in $\mathbb R^n\times\mathbb R^m\times\mathbb R^n$; the Newton run is a sequence each of whose terms is a Newton step from the previous one. Assumptions (2.4)–(2.5) are implied by the strictly feasible starting point.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 32, Theorem 7.1, (7.1)–(7.4); pp. 31–32, Algorithm 7.1

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures
import Definitions.Def_SelfScaledIPM_FuncProx_Directions

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Theorem 7.1** (p. 32), one iteration of Algorithm 7.1. Fix `Δ > 0` and `κ ∈ (0, 1)`. There are
constants `ω₁, ω₂ > 0` depending only on `Δ` and `κ` such that the following holds for every proper
cone `K`, ν-self-scaled barrier `F`, problem data `(A, b, c)` with `A` surjective, and
`β = κ − ln(1 + κ)`. Let `(x, y, s) ∈ F(β)` (strictly feasible, `γ_F(x, s) ≤ β`), `w` its scaling
point, `(p_x, p_y, p_s)` its affine-scaling direction, `α` the largest step in `[0, 1)` whose whole
segment `[0, α]` keeps `x − α'p_x ∈ int K`, `s − α'p_s ∈ int K*` and with
`γ_F(x − αp_x, s − αp_s) = β + Δ`, and `z` a run of the Newton process (5.25) started at
`(x − αp_x, y − αp_y, s − αp_s)`. Then
(7.2) `α²/(1 − α) ≥ ω₁/ν`;
(7.3) `α²/(1 − α) ≥ ω₂/(|p_x|_x ‖p_s‖_s) ≥ ω₂/(√ν |p_x|_x |p_s|_s)`;
and the first index `N` with `z N ∈ F(β)` exists, satisfies
(7.4) `N ≤ ⌈Δ/(τ̄ − ln(1 + τ̄))⌉`, `τ̄ = ½ √(3β/(1 + β))`, and
(7.1) `⟨s_N, x_N⟩ ≤ (1 − α)⟨s, x⟩` for `z N = (x_N, y_N, s_N)`. -/
theorem theorem_7_1 (Δ κ : ℝ) (hΔ : 0 < Δ) (hκ₀ : 0 < κ) (hκ₁ : κ < 1) :
    ∃ ω₁ ω₂ : ℝ, 0 < ω₁ ∧ 0 < ω₂ ∧
    ∀ {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
      (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
      (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
      (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : β = κ - Real.log (1 + κ))
      (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
      (hstart : InFuncNbhd K F ν A b c β (x, y, s))
      (w : EuclideanSpace ℝ (Fin n)) (hw : SelfScaledIPM.ShortStep.IsScalingPoint K F x s w)
      (px : EuclideanSpace ℝ (Fin n)) (py : EuclideanSpace ℝ (Fin m)) (ps : EuclideanSpace ℝ (Fin n))
      (hp : IsAffineScalingDir A F s w px py ps)
      (α : ℝ)
      (hα : IsGreatest {a : ℝ | 0 ≤ a ∧ a < 1 ∧
          (∀ a' ∈ Set.Icc (0 : ℝ) a,
            x - a' • px ∈ interior K ∧ s - a' • ps ∈ interior (ConvexOptimization.dualCone K)) ∧
          gammaF K F ν (x - a • px) (s - a • ps) = β + Δ} α)
      (z : ℕ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
      (hz0 : z 0 = (x - α • px, y - α • py, s - α • ps))
      (hz : IsNewtonRun K F ν A z),
      ω₁ / ν ≤ α ^ 2 / (1 - α) ∧
      ω₂ / (SelfScaledIPM.ShortStep.absn K x px * SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps) ≤ α ^ 2 / (1 - α) ∧
      ω₂ / (Real.sqrt ν * SelfScaledIPM.ShortStep.absn K x px * SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) s ps) ≤
        ω₂ / (SelfScaledIPM.ShortStep.absn K x px * SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps) ∧
      ∃ N : ℕ, InFuncNbhd K F ν A b c β (z N) ∧
        (∀ j < N, β < gammaF K F ν (z j).1 (z j).2.2) ∧
        N ≤ ⌈Δ / ((1 / 2 : ℝ) * Real.sqrt (3 * β / (1 + β)) -
              Real.log (1 + (1 / 2 : ℝ) * Real.sqrt (3 * β / (1 + β))))⌉₊ ∧
        ⟪(z N).2.2, (z N).1⟫_ℝ ≤ (1 - α) * ⟪s, x⟫_ℝ := by sorry

end SelfScaledIPM.FuncProx
