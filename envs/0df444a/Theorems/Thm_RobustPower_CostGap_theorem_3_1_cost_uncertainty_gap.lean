-- Prove2me | Theorems.Thm_RobustPower_CostGap_theorem_3_1_cost_uncertainty_gap
-- name    : RobustPower.CostGap.theorem_3_1_cost_uncertainty_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:22:29.75588+00:00
-- url     : https://prove2.me/theorems/22b94b84-3374-42fb-8c52-85e19bea805b
-- title:
--   Theorem 3.1 — with uniform hypercube cost uncertainty, z_Rob(b, d) ≥ (n + 1) · z_Stoch(b, d)
-- statement:
--   Consider the instances of the stochastic problem $\Pi_{\mathrm{Stoch}}(b,d)$ and the robust problem $\Pi_{\mathrm{Rob}}(b,d)$ with no first-stage variables ($n_1=0$, so $c=0$ and $A=0$), $n_2=n\ge1$ continuous second-stage variables ($p_2=0$), and a single constraint ($m=1$) with $B=[1,1,\dots,1]\in\mathbb R^{1\times n}$. The right-hand side is $b(\omega)=1$ in every scenario, so the constraint reads $y_1+\dots+y_n\ge1$. Let $(\Omega,\mu)$ be a probability space of scenarios and $d:\Omega\to\mathbb R^n$ a measurable cost map such that
--
--   1. the uncertainty set is $I_{(b,d)}(\Omega)=\{(1,d(\omega)):\omega\in\Omega\}=\{1\}\times[0,1]^n$, that is, the range of $d$ is exactly the cube $[0,1]^n$;
--   2. the coordinates $d_1,\dots,d_n$ are independent and each uniformly distributed on $[0,1]$ under $\mu$.
--
--   Then
--
--   $$
--   z_{\mathrm{Rob}}(b,d)\ \ge\ (n+1)\cdot z_{\mathrm{Stoch}}(b,d).
--   $$
--
--   The uncertainty set and the measure are both symmetric and there are no integer variables: these are the hypotheses under which, for right-hand-side uncertainty alone, the robust optimum is at most twice the stochastic one (Theorem 2.1). Theorem 3.1 shows that this bound fails once the costs are uncertain: the stochasticity gap grows linearly in the dimension.
--
--   **Formalization Note** Both optimal values are infima in the extended reals, the stochastic problem ranges over integrable policies whose constraints hold in every scenario, and neither problem is assumed to have an optimal solution. The hypothesis $n\ge1$ is implicit in the paper. Independence and uniformity are stated as: the law of $d$ under $\mu$ equals the product of $n$ uniform distributions on $[0,1]$.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 22, Theorem 3.1 (proof pp. 22–23)

import Mathlib
import Definitions.Def_RobustPower_CostGap_Problems

open MeasureTheory Matrix

namespace RobustPower.CostGap

/-- Theorem 3.1 (p. 22). The instance `n₁ = 0`, `n₂ = n`, `p₂ = 0`, `m = 1`, `c = 0`, `A = 0`,
`B = [1, …, 1]`, `b(ω) = 1`, with uncertainty set `{1} × [0, 1]ⁿ` and the coordinates of `d`
independent and uniform on `[0, 1]`, has `z_Rob(b, d) ≥ (n + 1) · z_Stoch(b, d)`. -/
theorem theorem_3_1_cost_uncertainty_gap {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d) (hrange : Set.range d = Set.Icc 0 1)
    (hlaw : μ.map d = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :
    (((n : ℝ) + 1 : ℝ) : EReal) *
        zStochBD μ (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
          (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ ≤
      zRobBD (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
          (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ := by sorry

end RobustPower.CostGap
