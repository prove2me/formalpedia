-- Prove2me | Theorems.Thm_UnifiedFBSDE_Main_theorem_5_9
-- name    : UnifiedFBSDE.Main.theorem_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:18.850957+00:00
-- url     : https://prove2.me/theorems/babf5e8d-7c91-40d0-a080-46cf8022c0a3
-- title:
--   Theorem 5.9, p. 25 — under (5.14) the dominating ODEs (3.13) have solutions with −c₃ ≤ y̲ ≤ ȳ ≤ c₃
-- statement:
--   Let $T>0$, $K_0>0$ and $c_1,c_2,c_3$ satisfy (5.13): $c_1>0$, $0<c_2<c_3$, $c_1c_3<1$. Then there is $\varepsilon>0$, depending only on $T,K_0,c_1,c_2,c_3$, with the following property. For every FBSDE (1.1) on $[0,T]$ driven by a Brownian motion with its augmented filtration, whose coefficients satisfy Assumption 2.1 with Lipschitz constant $K_0$ and, uniformly for all $\theta_j$,
--
--   $$
--   |\sigma_3|\le c_1,\qquad |h|\le c_2,\qquad \overline F(t,c_3)\le\varepsilon,\qquad \underline F(t,-c_3)\ge-\varepsilon,\tag{5.14}
--   $$
--
--   the dominating ODEs (3.13) have solutions $\overline y,\underline y$ with
--
--   $$
--   -c_3\le\underline y_t\le\overline y_t\le c_3,\qquad t\in[0,T],
--   $$
--
--   and both $\overline y$ and $\underline y$ satisfy (5.9): they are bounded and $(1-\sigma_3y)^{-1}$ is bounded.
--
--   This is the "Case I" a priori bound; with Theorem 6.1 it yields a Lipschitz decoupling field over any horizon.
--
--   **Formalization Note** "$\varepsilon=\varepsilon(T)>0$ small enough" is an existential placed after $T,K_0,c_1,c_2,c_3$ and before the probability space and coefficients, so $\varepsilon$ cannot be tuned to a particular coefficient set. (5.9) is stated as $\kappa\le|1-\tilde\sigma_3(t,\theta_1,\theta_2)y_t|$ for some $\kappa>0$, for all $t$, a.s., for all $\theta_j$.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 25, (5.13), Theorem 5.9, (5.14); p. 22, (5.9)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_UnifiedFBSDE_Main_Setting
import Definitions.Def_UnifiedFBSDE_Main_Dominating

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace UnifiedFBSDE.Main

theorem theorem_5_9 :
    ∀ T : ℝ≥0, 0 < T → ∀ K₀ c₁ c₂ c₃ : ℝ, 0 < K₀ → Cond513 c₁ c₂ c₃ →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (c : Coeffs Ω),
          Assumption21 (ReflectedBSDE.Existence.augmentedFiltration P hB) P T K₀ c →
          Cond514 c P T ε c₁ c₂ c₃ →
            ∃ ybar yund : ℝ → ℝ, SolvesUpperODE c P T ybar ∧ SolvesLowerODE c P T yund ∧
              (∀ t ∈ Icc (0 : ℝ) T, -c₃ ≤ yund t ∧ yund t ≤ ybar t ∧ ybar t ≤ c₃) ∧
              Cond59 c P T ybar ∧ Cond59 c P T yund := by sorry

end UnifiedFBSDE.Main
