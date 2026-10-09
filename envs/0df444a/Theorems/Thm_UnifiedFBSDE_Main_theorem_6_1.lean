-- Prove2me | Theorems.Thm_UnifiedFBSDE_Main_theorem_6_1
-- name    : UnifiedFBSDE.Main.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:16.026426+00:00
-- url     : https://prove2.me/theorems/09222f75-b4ac-499f-b03d-79082e8cc5c2
-- title:
--   Theorem 6.1, p. 28 — if |σ₃| ≤ c₁, |h| ≤ c₂, c₁c₂ < 1, then for small T the FBSDE is well posed with −c̃₂ ≤ y̲ ≤ ȳ ≤ c̃₂ and y̲ ≤ ∂ₓu ≤ ȳ
-- statement:
--   Let $K_0>0$ and $c_1,c_2>0$ with $c_1c_2<1$ (6.1), and set $\tilde c_2=(c_2+c_1^{-1})/2$, so that $c_2<\tilde c_2<c_1^{-1}$. There is $\delta>0$, depending only on $c_1,c_2,K_0$, such that for every $T\in(0,\delta]$ and every FBSDE (1.1) on $[0,T]$ satisfying Assumption 2.1 with Lipschitz constant $K_0$ and, uniformly for all $\theta_j$, $|\sigma_3|\le c_1$ and $|h|\le c_2$:
--
--   1. for every $x$, the FBSDE (1.1) has a unique solution $\Theta\in\mathbb L^2$;
--   2. the ODEs (3.13) have solutions $\overline y,\underline y$ with
--   $$-\tilde c_2\le\underline y_t\le\overline y_t\le\tilde c_2,\qquad t\in[0,T];\tag{6.2}$$
--   3. there is a random field $u$ such that $Y_t=u(t,X_t)$ for all $t\in[0,T]$ along the solution from every $x$, and
--   $$\underline y_t\le\frac{u(t,x_1)-u(t,x_2)}{x_1-x_2}\le\overline y_t\qquad\text{for any }x_1\ne x_2.\tag{6.3}$$
--
--   This is the local building block of the paper: on a short interval the FBSDE is well posed and its decoupling field is Lipschitz with slopes controlled by the dominating ODEs.
--
--   **Formalization Note** $\delta$ is an existential placed after $K_0,c_1,c_2$ and before $T$ and the coefficients. In (iii), $Y_t=u(t,X_t)$ holds a.s. for each $t$, and (6.3) holds, for each $t$ and each pair $x_1\ne x_2$, almost surely (the null set may depend on $x_1,x_2$).
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 27, (6.1), definition of c̃₂; p. 28, Theorem 6.1, (6.2), (6.3)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_UnifiedFBSDE_Main_Setting
import Definitions.Def_UnifiedFBSDE_Main_Dominating

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace UnifiedFBSDE.Main

theorem theorem_6_1 :
    ∀ K₀ c₁ c₂ : ℝ, 0 < K₀ → 0 < c₁ → 0 < c₂ → c₁ * c₂ < 1 →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ T : ℝ≥0, 0 < T → (T : ℝ) ≤ δ →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (c : Coeffs Ω),
          Assumption21 (ReflectedBSDE.Existence.augmentedFiltration P hB) P T K₀ c →
          UnifCoef P T (fun t ω θ₁ θ₂ => |dq3 c.σ t ω θ₁ θ₂| ≤ c₁) →
          UnifTerm P (fun ω x₁ x₂ => |htil c ω x₁ x₂| ≤ c₂) →
            SmallTimeConclusion (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T
              (fun lo hi => -((c₂ + c₁⁻¹) / 2) ≤ lo ∧ lo ≤ hi ∧ hi ≤ (c₂ + c₁⁻¹) / 2) := by sorry

end UnifiedFBSDE.Main
