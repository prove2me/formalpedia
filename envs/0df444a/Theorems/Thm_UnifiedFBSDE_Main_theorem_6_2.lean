-- Prove2me | Theorems.Thm_UnifiedFBSDE_Main_theorem_6_2
-- name    : UnifiedFBSDE.Main.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:38.09887+00:00
-- url     : https://prove2.me/theorems/1bb3fe5f-6f6b-4806-a033-501a04e7618c
-- title:
--   Theorem 6.2, p. 29 — if σ₃, h satisfy one of (5.15)–(5.18), then Theorem 6.1 holds for small T with the band y̲ ≥ c̃₂⁻¹ or ȳ ≤ −c̃₂⁻¹
-- statement:
--   Let $K_0>0$ and $c_1,c_2>0$ with $c_1c_2<1$, and $\tilde c_2=(c_2+c_1^{-1})/2$. There is $\delta>0$, depending only on $c_1,c_2,K_0$, such that for every $T\in(0,\delta]$ and every FBSDE (1.1) satisfying Assumption 2.1 with constant $K_0$, if $\sigma_3$ and $h$ satisfy (uniformly for all $\theta_j$) one of the conditions of (5.15)–(5.18),
--
--   $$
--   \sigma_3\ge c_1^{-1},\ h\ge c_2^{-1};\quad \sigma_3\le-c_1^{-1},\ h\ge c_2^{-1};\quad \sigma_3\ge c_1^{-1},\ h\le-c_2^{-1};\quad \sigma_3\le-c_1^{-1},\ h\le-c_2^{-1},
--   $$
--
--   then all conclusions of Theorem 6.1 hold — unique solvability in $\mathbb L^2$, solutions $\overline y,\underline y$ of (3.13), and a random field $u$ with $Y_t=u(t,X_t)$ and $\underline y_t\le(u(t,x_1)-u(t,x_2))/(x_1-x_2)\le\overline y_t$ — except that (6.2) is replaced by $\overline y\ge\underline y\ge\tilde c_2^{-1}$ in the first two cases and by $\underline y\le\overline y\le-\tilde c_2^{-1}$ in the last two.
--
--   This is the small-duration result for Case II, where $\sigma_3$ and $h$ are large.
--
--   **Formalization Note** "$\sigma_3$ and $h$ satisfy one of the conditions in (5.15)–(5.18)" is read as the conditions on $\sigma_3$ and $h$ only, as the proof uses them; the $\varepsilon$-conditions on $\underline F,\overline F,\alpha_3$ are not part of Theorem 6.2. Each case is a separate implication.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 29, Theorem 6.2

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_UnifiedFBSDE_Main_Setting
import Definitions.Def_UnifiedFBSDE_Main_Dominating

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace UnifiedFBSDE.Main

theorem theorem_6_2 :
    ∀ K₀ c₁ c₂ : ℝ, 0 < K₀ → 0 < c₁ → 0 < c₂ → c₁ * c₂ < 1 →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ T : ℝ≥0, 0 < T → (T : ℝ) ≤ δ →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (c : Coeffs Ω),
          Assumption21 (ReflectedBSDE.Existence.augmentedFiltration P hB) P T K₀ c →
            -- (5.15): σ₃ ≥ c₁⁻¹, h ≥ c₂⁻¹
            (UnifCoef P T (fun t ω θ₁ θ₂ => c₁⁻¹ ≤ dq3 c.σ t ω θ₁ θ₂) →
              UnifTerm P (fun ω x₁ x₂ => c₂⁻¹ ≤ htil c ω x₁ x₂) →
              SmallTimeConclusion (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T
                (fun lo hi => ((c₂ + c₁⁻¹) / 2)⁻¹ ≤ lo ∧ lo ≤ hi)) ∧
            -- (5.16): σ₃ ≤ −c₁⁻¹, h ≥ c₂⁻¹
            (UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≤ -c₁⁻¹) →
              UnifTerm P (fun ω x₁ x₂ => c₂⁻¹ ≤ htil c ω x₁ x₂) →
              SmallTimeConclusion (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T
                (fun lo hi => ((c₂ + c₁⁻¹) / 2)⁻¹ ≤ lo ∧ lo ≤ hi)) ∧
            -- (5.17): σ₃ ≥ c₁⁻¹, h ≤ −c₂⁻¹
            (UnifCoef P T (fun t ω θ₁ θ₂ => c₁⁻¹ ≤ dq3 c.σ t ω θ₁ θ₂) →
              UnifTerm P (fun ω x₁ x₂ => htil c ω x₁ x₂ ≤ -c₂⁻¹) →
              SmallTimeConclusion (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T
                (fun lo hi => lo ≤ hi ∧ hi ≤ -((c₂ + c₁⁻¹) / 2)⁻¹)) ∧
            -- (5.18): σ₃ ≤ −c₁⁻¹, h ≤ −c₂⁻¹
            (UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≤ -c₁⁻¹) →
              UnifTerm P (fun ω x₁ x₂ => htil c ω x₁ x₂ ≤ -c₂⁻¹) →
              SmallTimeConclusion (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T
                (fun lo hi => lo ≤ hi ∧ hi ≤ -((c₂ + c₁⁻¹) / 2)⁻¹)) := by sorry

end UnifiedFBSDE.Main
