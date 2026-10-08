-- Prove2me | Theorems.Thm_RobustPower_CostGap_eq_3_1_stoch_le_expected_min
-- name    : RobustPower.CostGap.eq_3_1_stoch_le_expected_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:22:37.840253+00:00
-- url     : https://prove2.me/theorems/2207e792-6dab-4668-a5e7-4720093bd39b
-- title:
--   Eq. (3.1), p. 23 — z_Stoch(b, d) ≤ E_µ[min(d₁(ω), …, dₙ(ω))] in the instance of Theorem 3.1
-- statement:
--   Consider the instance of Theorem 3.1 ($n_1=0$, $c=0$, $A=0$, $n\ge1$ continuous second-stage variables, $B=[1,\dots,1]\in\mathbb R^{1\times n}$, $b(\omega)=1$), with a probability measure $\mu$ on the scenario set $\Omega$ and a measurable cost map $d:\Omega\to\mathbb R^n$ whose range is exactly $[0,1]^n$. Then the optimal value of the stochastic problem $\Pi_{\mathrm{Stoch}}(b,d)$ satisfies
--
--   $$
--   z_{\mathrm{Stoch}}(b,d)\ \le\ \mathbb E_\mu\bigl[\min\bigl(d_1(\omega),\dots,d_n(\omega)\bigr)\bigr].
--   $$
--
--   The paper obtains this bound from a policy that, in each scenario, buys one unit of a cheapest coordinate. No distributional assumption on $d$ is used beyond measurability and boundedness; combined with Eq. (3.2) it gives $z_{\mathrm{Stoch}}(b,d)\le 1/(n+1)$.
--
--   **Formalization Note** $z_{\mathrm{Stoch}}$ is the extended-real infimum of (1.4) over integrable policies. The paper's policy $\tilde y$ puts a 1 on every minimizing coordinate, which at ties costs a multiple of the minimum; the statement here is the resulting bound on $z_{\mathrm{Stoch}}$, not a claim about that particular policy. The minimum is written as an infimum over the finite nonempty index set $\{1,\dots,n\}$.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 23, proof of Theorem 3.1, Eq. (3.1)

import Mathlib
import Definitions.Def_RobustPower_CostGap_Problems

open MeasureTheory Matrix

namespace RobustPower.CostGap

/-- Eq. (3.1), p. 23: in the instance of Theorem 3.1, the policy that buys one unit of a cheapest
coordinate shows `z_Stoch(b, d) ≤ E_μ[min(d₁(ω), …, dₙ(ω))]`. -/
theorem eq_3_1_stoch_le_expected_min {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d) (hrange : Set.range d = Set.Icc 0 1) :
    zStochBD μ (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
        (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ ≤
      ((∫ ω, (⨅ j, d ω j) ∂μ : ℝ) : EReal) := by sorry

end RobustPower.CostGap
