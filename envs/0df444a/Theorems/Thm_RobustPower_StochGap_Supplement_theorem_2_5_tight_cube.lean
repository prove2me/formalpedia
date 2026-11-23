-- Prove2me | Theorems.Thm_RobustPower_StochGap_Supplement_theorem_2_5_tight_cube
-- name    : RobustPower.StochGap.Supplement.theorem_2_5_tight_cube
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:32:28.454915+00:00
-- url     : https://prove2.me/theorems/a1a4b2a3-7ae8-4563-95fe-814de61e3992
-- title:
--   Theorem 2.5, p. 18 — the stochasticity gap 2 is attained on the unit cube with uniform independent coordinates
-- statement:
--   Consider the instance of §2.2: there is no first stage ($n_1=0$, $A=0$, $c=0$), $n_2=m=n$, $B=I_n$, $d=(1,\dots,1)$, no integer variables, the uncertainty set is the unit cube
--   $$I_b(\Omega)=\{b\in\mathbb R^n_+ : 0\le b_j\le 1,\ j=1,\dots,n\},$$
--   and under $\mu$ the coordinates $b_1,\dots,b_n$ are independent and uniformly distributed on $[0,1]$. Then
--   $$z_{\mathrm{Rob}}(b)=2\, z_{\mathrm{Stoch}}(b).$$
--
--   Here $z_{\mathrm{Rob}}(b)=n$ and $z_{\mathrm{Stoch}}(b)=n/2$, so the factor $2$ of Theorem 2.1 cannot be improved for symmetric uncertainty sets.
--
--   **Formalization Note** $b:\Omega\to\mathbb R^n$ is measurable with range exactly the unit cube, and the law of $b$ under $\mu$ is Lebesgue measure restricted to $[0,1]^n$, which is the product of $n$ uniform laws on $[0,1]$. Optimal values are the published EReal infima of the base mission.
--
--   Differences from the source:
--
--   - encoding: optimal values defined by min over feasible solutions → EReal infima over the feasible set (⊤ when infeasible), no optimal solution assumed; reason: the published model of the base mission; the infimum equals the minimum whenever one is attained
--   - reading: each bⱼ is uniform on [0, 1] and independent of the other components → b is measurable and its law under μ is Lebesgue measure restricted to the unit cube [0, 1]ⁿ; reason: the product of n independent uniform laws on [0, 1] is exactly that measure
--   - reading: the instance does not repeat p₂ = 0 → no integer variables (I₂ = ∅); reason: §2 assumes p₂ = 0 throughout and p. 18 says the instance satisfies the assumptions of Theorem 2.1, which include p₂ = 0
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 18, instance of §2.2 and Theorem 2.5

import Mathlib
import Definitions.Def_RobustPower_StochGap_Problems

open MeasureTheory Matrix

namespace RobustPower.StochGap.Supplement

/-- Theorem 2.5 (p. 18): the instance of §2.2 with `n₁ = 0`, `n₂ = m = n`, `A = 0`, `c = 0`,
`d = (1, …, 1)`, `B = Iₙ`, no integer variables, uncertainty set the unit cube `[0, 1]ⁿ`, and
`μ` making the coordinates of `b` independent and uniform on `[0, 1]` (the law of `b` is
Lebesgue measure on the unit cube). Then `z_Rob(b) = 2 · z_Stoch(b)`. -/
theorem theorem_2_5_tight_cube {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → Fin n → ℝ)
    (hbmeas : Measurable b) (hrange : Set.range b = Set.Icc (0 : Fin n → ℝ) 1)
    (hlaw : μ.map b = volume.restrict (Set.Icc (0 : Fin n → ℝ) 1)) :
    RobustPower.StochGap.zRob (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ)
        b ∅ ∅ 0 (fun _ => 1) =
      2 * RobustPower.StochGap.zStoch μ (0 : Matrix (Fin n) (Fin 0) ℝ)
        (1 : Matrix (Fin n) (Fin n) ℝ) b ∅ ∅ 0 (fun _ => 1) := by sorry

end RobustPower.StochGap.Supplement
