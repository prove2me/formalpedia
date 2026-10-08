-- Prove2me | Theorems.Thm_StochConvexProg_Duality_theorem_3
-- name    : StochConvexProg.Duality.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:03.941721+00:00
-- url     : https://prove2.me/theorems/4220f44f-4ea8-4ed9-a2e4-d18e621e0909
-- title:
--   Theorem 3 — with C₁, C₂ bounded, min P = sup D > −∞, and φ is proper, convex, weakly lsc, attained, with φ** = φ
-- statement:
--   Assume the standing assumptions of the two-stage stochastic convex program, with $\sigma$ a probability measure, and suppose the sets $C_1$ and $C_2$ are bounded. Then
--   $$\min\mathbf P=\sup\mathbf D>-\infty,$$
--   that is, the infimum of $F(x,0)$ over $x\in X$ is attained, equals $\sup_{y\in Y}g(y)$, and this common value is not $-\infty$. In fact:
--
--   1. the perturbation function $\varphi(u)=\inf_{x\in X}F(x,u)$ is a proper convex function on $U$;
--   2. $\varphi$ is lower semicontinuous with respect to the weak topology on $U$ induced by the pairing (1.6) with $Y$;
--   3. the infimum defining $\varphi$ is always attained: for each $u\in U$ there is $x\in X$ with $F(x,u)=\varphi(u)$;
--   4. in particular $\varphi^{**}=\varphi$, the biconjugate being taken with respect to (1.6).
--
--   This is the basic duality theorem of the paper: under bounded constraint sets there is no duality gap between the stochastic program and its Lagrangian dual over $Y=\mathbb R^{m_1}\times\mathcal L^1_{m_2}$, and the primal problem has a solution.
--
--   **Formalization Note** "min" is formalized as "the infimum is attained". All values are in `EReal`, so $\min\mathbf P=+\infty$ (an infeasible problem) is allowed, as in the paper. Convexity of $\varphi$ is convexity of its epigraph; properness is "never $-\infty$, somewhere finite". The weak topology on $U$ is passed explicitly; lower semicontinuity in the norm topology would be a weaker statement.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 189, Theorem 3

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem
import Definitions.Def_StochConvexProg_Duality_Dual

open MeasureTheory

namespace StochConvexProg.Duality

/-- Rockafellar–Wets (1976), p. 189, Theorem 3: if `C₁` and `C₂` are bounded, then
`min P = sup D > −∞`; in fact `φ` is a proper convex function on `U`, lower semicontinuous for
the weak topology on `U` induced by the pairing with `Y`, the infimum defining `φ` is always
attained, and `φ** = φ`. -/
theorem theorem_3 {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂)
    (hC₁ : Bornology.IsBounded pr.C₁) (hC₂ : Bornology.IsBounded pr.C₂) :
    (∃ x : XSpace σ n₁ n₂, pr.F x 0 = pr.infP) ∧ pr.infP = pr.supD ∧ ⊥ < pr.supD ∧
      EProper pr.phi ∧ EConvex pr.phi ∧
      @LowerSemicontinuous (USpace σ m₁ m₂) EReal (weakU σ m₁ m₂) _ pr.phi ∧
      (∀ u : USpace σ m₁ m₂, ∃ x : XSpace σ n₁ n₂, pr.F x u = pr.phi u) ∧
      biconjU pr.phi = pr.phi := by sorry

end StochConvexProg.Duality
