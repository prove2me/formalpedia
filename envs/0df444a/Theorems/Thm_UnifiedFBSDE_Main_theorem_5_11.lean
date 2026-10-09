-- Prove2me | Theorems.Thm_UnifiedFBSDE_Main_theorem_5_11
-- name    : UnifiedFBSDE.Main.theorem_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:25.649891+00:00
-- url     : https://prove2.me/theorems/8838d069-dbdb-4468-8be4-b81b2b995f72
-- title:
--   Theorem 5.11, pp. 26–27 — under one of (5.19)–(5.22) the dominating ODEs have bounded solutions keeping the bound of h with c₃
-- statement:
--   Let $T>0$, $K_0>0$ and $c_1,c_2,c_3$ satisfy (5.13). There is $\varepsilon>0$, depending only on these data, such that for every FBSDE (1.1) satisfying Assumption 2.1 with constant $K_0$ the following holds, with all conditions uniform in $\theta_j$ and $\alpha_3=b_2-b_3\sigma_2/\sigma_3$. The ODEs (3.13) have bounded solutions $\overline y,\underline y$, both satisfying (5.9), and for all $t\in[0,T]$:
--
--   1. under (5.19) $\sigma_3\le c_1$, $0\le h\le c_2$, $\overline F(t,c_3)\le\varepsilon$, $f_1\ge0$: $0\le\overline y_t,\underline y_t\le c_3$;
--   2. under (5.20) $0\le\sigma_3\le c_1$, $h\le c_2$, $\overline F(t,c_3)\le\varepsilon$, $\alpha_3\ge-\varepsilon$: $\overline y_t,\underline y_t\le c_3$;
--   3. under (5.21) $\sigma_3\ge-c_1$, $0\ge h\ge-c_2$, $\underline F(t,-c_3)\ge-\varepsilon$, $f_1\le0$: $-c_3\le\overline y_t,\underline y_t\le0$;
--   4. under (5.22) $0\ge\sigma_3\ge-c_1$, $h\ge-c_2$, $\underline F(t,-c_3)\ge-\varepsilon$, $\alpha_3\le\varepsilon$: $\overline y_t,\underline y_t\ge-c_3$.
--
--   In each case the solutions satisfy "the corresponding property of $h$ with $c_2$ replaced by $c_3$", for instance under (5.19)
--
--   $$
--   0\le h\le c_2\quad\Longrightarrow\quad 0\le\underline y_t,\ \overline y_t\le c_3 .
--   $$
--
--   This is "Case III" of the paper (Table 3), where $\sigma_3h\le c_1c_2$ and one of $\sigma_3,h$ keeps a sign.
--
--   **Formalization Note** One $\varepsilon$ for all four cases, before the probability space; each case is a separate implication with its own solutions. In (5.20) and (5.22) the condition on $\alpha_3$ carries $\tilde\sigma_3\ne0$, since $\alpha_3$ divides by $\sigma_3$.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, pp. 26–27, Theorem 5.11, (5.19)–(5.22)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_UnifiedFBSDE_Main_Setting
import Definitions.Def_UnifiedFBSDE_Main_Dominating

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace UnifiedFBSDE.Main

theorem theorem_5_11 :
    ∀ T : ℝ≥0, 0 < T → ∀ K₀ c₁ c₂ c₃ : ℝ, 0 < K₀ → Cond513 c₁ c₂ c₃ →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (c : Coeffs Ω),
          Assumption21 (ReflectedBSDE.Existence.augmentedFiltration P hB) P T K₀ c →
            (Cond519 c P T ε c₁ c₂ c₃ →
              ∃ ybar yund : ℝ → ℝ, SolvesUpperODE c P T ybar ∧ SolvesLowerODE c P T yund ∧
                BoundedOn T ybar ∧ BoundedOn T yund ∧
                (∀ t ∈ Icc (0 : ℝ) T, (0 ≤ ybar t ∧ ybar t ≤ c₃) ∧ (0 ≤ yund t ∧ yund t ≤ c₃)) ∧
                Cond59 c P T ybar ∧ Cond59 c P T yund) ∧
            (Cond520 c P T ε c₁ c₂ c₃ →
              ∃ ybar yund : ℝ → ℝ, SolvesUpperODE c P T ybar ∧ SolvesLowerODE c P T yund ∧
                BoundedOn T ybar ∧ BoundedOn T yund ∧
                (∀ t ∈ Icc (0 : ℝ) T, ybar t ≤ c₃ ∧ yund t ≤ c₃) ∧
                Cond59 c P T ybar ∧ Cond59 c P T yund) ∧
            (Cond521 c P T ε c₁ c₂ c₃ →
              ∃ ybar yund : ℝ → ℝ, SolvesUpperODE c P T ybar ∧ SolvesLowerODE c P T yund ∧
                BoundedOn T ybar ∧ BoundedOn T yund ∧
                (∀ t ∈ Icc (0 : ℝ) T, (-c₃ ≤ ybar t ∧ ybar t ≤ 0) ∧ (-c₃ ≤ yund t ∧ yund t ≤ 0)) ∧
                Cond59 c P T ybar ∧ Cond59 c P T yund) ∧
            (Cond522 c P T ε c₁ c₂ c₃ →
              ∃ ybar yund : ℝ → ℝ, SolvesUpperODE c P T ybar ∧ SolvesLowerODE c P T yund ∧
                BoundedOn T ybar ∧ BoundedOn T yund ∧
                (∀ t ∈ Icc (0 : ℝ) T, -c₃ ≤ ybar t ∧ -c₃ ≤ yund t) ∧
                Cond59 c P T ybar ∧ Cond59 c P T yund) := by sorry

end UnifiedFBSDE.Main
