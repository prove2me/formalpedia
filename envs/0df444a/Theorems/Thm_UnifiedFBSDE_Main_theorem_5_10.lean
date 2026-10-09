-- Prove2me | Theorems.Thm_UnifiedFBSDE_Main_theorem_5_10
-- name    : UnifiedFBSDE.Main.theorem_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:27.816922+00:00
-- url     : https://prove2.me/theorems/a68a3211-aef1-4421-85d9-d29fa2bfd662
-- title:
--   Theorem 5.10, pp. 25–26 — under one of (5.15)–(5.18) the dominating ODEs have bounded solutions keeping the sign bound of h with c₃
-- statement:
--   Let $T>0$, $K_0>0$ and $c_1,c_2,c_3$ satisfy (5.13). There is $\varepsilon>0$, depending only on these data, such that for every FBSDE (1.1) satisfying Assumption 2.1 with constant $K_0$ the following holds, with all conditions uniform in $\theta_j$ and $\alpha_3=b_2-b_3\sigma_2/\sigma_3$:
--
--   1. under (5.15) $\sigma_3\ge c_1^{-1}$, $h\ge c_2^{-1}$, $\underline F(t,c_3^{-1})\ge-\varepsilon$, $\alpha_3\le\varepsilon$, or (5.16) $\sigma_3\le-c_1^{-1}$, $h\ge c_2^{-1}$, $\underline F(t,c_3^{-1})\ge-\varepsilon$, $\alpha_3\le\varepsilon$: the ODEs (3.13) have bounded solutions with $\overline y_t\ge c_3^{-1}$ and $\underline y_t\ge c_3^{-1}$;
--   2. under (5.17) $\sigma_3\ge c_1^{-1}$, $h\le-c_2^{-1}$, $\overline F(t,-c_3^{-1})\le\varepsilon$, $\alpha_3\ge-\varepsilon$, or (5.18) $\sigma_3\le-c_1^{-1}$, $h\le-c_2^{-1}$, $\overline F(t,-c_3^{-1})\le\varepsilon$, $\alpha_3\ge-\varepsilon$: the ODEs (3.13) have bounded solutions with $\overline y_t\le-c_3^{-1}$ and $\underline y_t\le-c_3^{-1}$.
--
--   In every case both solutions satisfy (5.9):
--
--   $$
--   \sup_{t\le T}|y_t|<\infty,\qquad \inf_{t,\theta_j}|1-\sigma_3y_t|>0 .
--   $$
--
--   This is "Case II" of the paper (Table 2): the terminal slope $h$ and $\sigma_3$ are both bounded away from $0$, and the dominating solutions inherit the bound on $h$ with $c_2$ replaced by $c_3$.
--
--   **Formalization Note** $\varepsilon$ is one existential for all four cases, placed before the probability space and coefficients. Each case is a separate implication with its own pair of solutions. Every occurrence of $\alpha_3$ carries $\tilde\sigma_3\ne0$ (automatic here, since $|\tilde\sigma_3|\ge c_1^{-1}$).
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, pp. 25–26, Theorem 5.10, (5.15)–(5.18)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_UnifiedFBSDE_Main_Setting
import Definitions.Def_UnifiedFBSDE_Main_Dominating

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace UnifiedFBSDE.Main

theorem theorem_5_10 :
    ∀ T : ℝ≥0, 0 < T → ∀ K₀ c₁ c₂ c₃ : ℝ, 0 < K₀ → Cond513 c₁ c₂ c₃ →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (c : Coeffs Ω),
          Assumption21 (ReflectedBSDE.Existence.augmentedFiltration P hB) P T K₀ c →
            (Cond515 c P T ε c₁ c₂ c₃ →
              ∃ ybar yund : ℝ → ℝ, SolvesUpperODE c P T ybar ∧ SolvesLowerODE c P T yund ∧
                BoundedOn T ybar ∧ BoundedOn T yund ∧
                (∀ t ∈ Icc (0 : ℝ) T, c₃⁻¹ ≤ ybar t ∧ c₃⁻¹ ≤ yund t) ∧
                Cond59 c P T ybar ∧ Cond59 c P T yund) ∧
            (Cond516 c P T ε c₁ c₂ c₃ →
              ∃ ybar yund : ℝ → ℝ, SolvesUpperODE c P T ybar ∧ SolvesLowerODE c P T yund ∧
                BoundedOn T ybar ∧ BoundedOn T yund ∧
                (∀ t ∈ Icc (0 : ℝ) T, c₃⁻¹ ≤ ybar t ∧ c₃⁻¹ ≤ yund t) ∧
                Cond59 c P T ybar ∧ Cond59 c P T yund) ∧
            (Cond517 c P T ε c₁ c₂ c₃ →
              ∃ ybar yund : ℝ → ℝ, SolvesUpperODE c P T ybar ∧ SolvesLowerODE c P T yund ∧
                BoundedOn T ybar ∧ BoundedOn T yund ∧
                (∀ t ∈ Icc (0 : ℝ) T, ybar t ≤ -c₃⁻¹ ∧ yund t ≤ -c₃⁻¹) ∧
                Cond59 c P T ybar ∧ Cond59 c P T yund) ∧
            (Cond518 c P T ε c₁ c₂ c₃ →
              ∃ ybar yund : ℝ → ℝ, SolvesUpperODE c P T ybar ∧ SolvesLowerODE c P T yund ∧
                BoundedOn T ybar ∧ BoundedOn T yund ∧
                (∀ t ∈ Icc (0 : ℝ) T, ybar t ≤ -c₃⁻¹ ∧ yund t ≤ -c₃⁻¹) ∧
                Cond59 c P T ybar ∧ Cond59 c P T yund) := by sorry

end UnifiedFBSDE.Main
