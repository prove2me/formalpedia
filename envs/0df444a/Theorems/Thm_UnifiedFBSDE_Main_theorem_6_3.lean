-- Prove2me | Theorems.Thm_UnifiedFBSDE_Main_theorem_6_3
-- name    : UnifiedFBSDE.Main.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:27.05134+00:00
-- url     : https://prove2.me/theorems/621b33ab-dfb6-4785-833e-410338225296
-- title:
--   Theorem 6.3, p. 31 — if σ₃, h satisfy one of (5.19)–(5.22), then Theorem 6.1 holds for small T with the corresponding one-sided bands
-- statement:
--   Let $K_0>0$ and $c_1,c_2>0$ with $c_1c_2<1$, and $\tilde c_2=(c_2+c_1^{-1})/2$. There is $\delta>0$, depending only on $c_1,c_2,K_0$, such that for every $T\in(0,\delta]$ and every FBSDE (1.1) satisfying Assumption 2.1 with constant $K_0$, if $\sigma_3$ and $h$ satisfy (uniformly for all $\theta_j$) one of the conditions of (5.19)–(5.22), then all conclusions of Theorem 6.1 hold, with (6.2) replaced by
--
--   $$
--   \begin{aligned}
--   0\le\underline y\le\overline y\le\tilde c_2 &\quad\text{under } \sigma_3\le c_1,\ 0\le h\le c_2\ (5.19);\\
--   \underline y\le\overline y\le\tilde c_2 &\quad\text{under } 0\le\sigma_3\le c_1,\ h\le c_2\ (5.20);\\
--   0\ge\overline y\ge\underline y\ge-\tilde c_2 &\quad\text{under } \sigma_3\ge-c_1,\ 0\ge h\ge-c_2\ (5.21);\\
--   \overline y\ge\underline y\ge-\tilde c_2 &\quad\text{under } 0\ge\sigma_3\ge-c_1,\ h\ge-c_2\ (5.22).
--   \end{aligned}
--   $$
--
--   This is the small-duration result for Case III.
--
--   **Formalization Note** As in Theorem 6.2, only the $\sigma_3$- and $h$-parts of (5.19)–(5.22) are hypotheses. Each case is a separate implication, because (5.19) and (5.20) can hold simultaneously.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 31, Theorem 6.3

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_UnifiedFBSDE_Main_Setting
import Definitions.Def_UnifiedFBSDE_Main_Dominating

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace UnifiedFBSDE.Main

theorem theorem_6_3 :
    ∀ K₀ c₁ c₂ : ℝ, 0 < K₀ → 0 < c₁ → 0 < c₂ → c₁ * c₂ < 1 →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ T : ℝ≥0, 0 < T → (T : ℝ) ≤ δ →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (c : Coeffs Ω),
          Assumption21 (ReflectedBSDE.Existence.augmentedFiltration P hB) P T K₀ c →
            -- (5.19): σ₃ ≤ c₁, 0 ≤ h ≤ c₂
            (UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≤ c₁) →
              UnifTerm P (fun ω x₁ x₂ => 0 ≤ htil c ω x₁ x₂ ∧ htil c ω x₁ x₂ ≤ c₂) →
              SmallTimeConclusion (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T
                (fun lo hi => 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ (c₂ + c₁⁻¹) / 2)) ∧
            -- (5.20): 0 ≤ σ₃ ≤ c₁, h ≤ c₂
            (UnifCoef P T (fun t ω θ₁ θ₂ => 0 ≤ dq3 c.σ t ω θ₁ θ₂ ∧ dq3 c.σ t ω θ₁ θ₂ ≤ c₁) →
              UnifTerm P (fun ω x₁ x₂ => htil c ω x₁ x₂ ≤ c₂) →
              SmallTimeConclusion (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T
                (fun lo hi => lo ≤ hi ∧ hi ≤ (c₂ + c₁⁻¹) / 2)) ∧
            -- (5.21): σ₃ ≥ −c₁, 0 ≥ h ≥ −c₂
            (UnifCoef P T (fun t ω θ₁ θ₂ => -c₁ ≤ dq3 c.σ t ω θ₁ θ₂) →
              UnifTerm P (fun ω x₁ x₂ => -c₂ ≤ htil c ω x₁ x₂ ∧ htil c ω x₁ x₂ ≤ 0) →
              SmallTimeConclusion (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T
                (fun lo hi => -((c₂ + c₁⁻¹) / 2) ≤ lo ∧ lo ≤ hi ∧ hi ≤ 0)) ∧
            -- (5.22): 0 ≥ σ₃ ≥ −c₁, h ≥ −c₂
            (UnifCoef P T (fun t ω θ₁ θ₂ => -c₁ ≤ dq3 c.σ t ω θ₁ θ₂ ∧ dq3 c.σ t ω θ₁ θ₂ ≤ 0) →
              UnifTerm P (fun ω x₁ x₂ => -c₂ ≤ htil c ω x₁ x₂) →
              SmallTimeConclusion (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T
                (fun lo hi => -((c₂ + c₁⁻¹) / 2) ≤ lo ∧ lo ≤ hi)) := by sorry

end UnifiedFBSDE.Main
