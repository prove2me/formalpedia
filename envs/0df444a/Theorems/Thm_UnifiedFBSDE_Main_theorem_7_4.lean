-- Prove2me | Theorems.Thm_UnifiedFBSDE_Main_theorem_7_4
-- name    : UnifiedFBSDE.Main.theorem_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:23.837335+00:00
-- url     : https://prove2.me/theorems/d08779a6-ad3e-4ea7-899d-683d8ea0b9d4
-- title:
--   Theorem 7.4, p. 35 — under Cases I–III the FBSDE has a decoupling field with bounded difference quotients and a unique L² solution with ‖Θ‖² ≤ C(|x|² + I₀²)
-- statement:
--   Let $T>0$, $K_0>0$ and $c_1,c_2,c_3$ satisfy (5.13): $c_1>0$, $0<c_2<c_3$, $c_1c_3<1$. There are $\varepsilon>0$ and $C>0$, depending only on $T,K_0,c_1,c_2,c_3$, such that the following holds for every FBSDE
--
--   $$
--   X_t=x+\int_0^tb(s,\Theta_s)ds+\int_0^t\sigma(s,\Theta_s)dB_s,\qquad
--   Y_t=g(X_T)+\int_t^Tf(s,\Theta_s)ds-\int_t^TZ_sdB_s,\qquad t\in[0,T],
--   $$
--
--   driven by a one-dimensional Brownian motion with its augmented natural filtration, whose coefficients satisfy Assumption 2.1 with Lipschitz constant $K_0$ and one of the conditions of Cases I–III (uniformly for all $\theta_j$, with $\alpha_3=b_2-b_3\sigma_2/\sigma_3$):
--
--   - **Case I** (5.14): $|\sigma_3|\le c_1$, $|h|\le c_2$, $\overline F(t,c_3)\le\varepsilon$, $\underline F(t,-c_3)\ge-\varepsilon$;
--   - **Case II** (Table 2, (5.15)–(5.18)): $|\sigma_3|\ge c_1^{-1}$, $|h|\ge c_2^{-1}$ with constant signs, and the corresponding bounds on $\underline F(t,c_3^{-1})$ or $\overline F(t,-c_3^{-1})$ and on $\alpha_3$;
--   - **Case III** (Table 3, (5.19)–(5.22), $\sigma_3\ne0$): $\sigma_3h\le c_1c_2$ with one of them of constant sign, and the corresponding bounds on $\overline F(t,c_3)$ or $\underline F(t,-c_3)$ and on $f_1$ or $\alpha_3$.
--
--   Then:
--
--   1. the FBSDE possesses a decoupling field $u$ whose difference quotient $(u(t,x_1)-u(t,x_2))/(x_1-x_2)$ satisfies the property assumed of $h$ with $c_2$ replaced by $c_3$ (for instance $|\cdot|\le c_3$ in Case I, $\ge c_3^{-1}$ under (5.15));
--   2. for every $x$ the FBSDE admits a unique solution $\Theta\in\mathbb L^2$, and
--   $$\|\Theta\|^2_{\mathbb L^2}\le C\,[\,|x|^2+I_0^2\,].\tag{7.2}$$
--
--   This is the main result of the paper: explicit, checkable conditions on the coefficients — through the dominating ODEs (3.13) — give well-posedness of a fully coupled FBSDE with random coefficients and $\sigma$ depending on $z$, over an arbitrary duration.
--
--   **Formalization Note** $\varepsilon$ ("given as that in Theorems 5.9, 5.10, 5.11") and $C$ are existentials placed after $T,K_0,c_1,c_2,c_3$ and before the probability space and the coefficients. Each of the nine conditions is a separate implication with its own decoupling field; the quotient bound holds for each $t$ and each $x_1\ne x_2$ almost surely. The heading "$\sigma_3\ne0$" of Table 3 is added to (5.19) and (5.21), and carried by the $\alpha_3$-condition in the other cases. $\|\Theta\|^2_{\mathbb L^2}$ and $I_0^2$ are computed in $[0,\infty]$. Solutions are unique only up to modification (each $X_t$, $Y_t$ almost surely), and a modification can raise $\sup_t|X_t|$ on a set of positive probability, so (7.2) is stated for *some* solution of the class (the version the paper means); a bound for every solution would be false already for zero coefficients and $x=0$.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 35, Cases I–III, Theorem 7.4, Table 2; p. 36, Table 3; p. 33, (7.2)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_UnifiedFBSDE_Main_Setting
import Definitions.Def_UnifiedFBSDE_Main_Dominating

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace UnifiedFBSDE.Main

theorem theorem_7_4 :
    ∀ T : ℝ≥0, 0 < T → ∀ K₀ c₁ c₂ c₃ : ℝ, 0 < K₀ → Cond513 c₁ c₂ c₃ →
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (c : Coeffs Ω),
          Assumption21 (ReflectedBSDE.Existence.augmentedFiltration P hB) P T K₀ c →
            -- (ii): under any of the conditions of Cases I–III, well-posedness and (7.2)
            ((Cond514 c P T ε c₁ c₂ c₃ ∨
                Cond515 c P T ε c₁ c₂ c₃ ∨ Cond516 c P T ε c₁ c₂ c₃ ∨
                Cond517 c P T ε c₁ c₂ c₃ ∨ Cond518 c P T ε c₁ c₂ c₃ ∨
                (Cond519 c P T ε c₁ c₂ c₃ ∧ SigmaNonzero c P T) ∨ Cond520 c P T ε c₁ c₂ c₃ ∨
                (Cond521 c P T ε c₁ c₂ c₃ ∧ SigmaNonzero c P T) ∨ Cond522 c P T ε c₁ c₂ c₃) →
              ∀ x : ℝ,
                HasUniqueSolution (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T x ∧
                ∃ X Y Z : ℝ≥0 → Ω → ℝ,
                  SolvesFBSDE (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T x X Y Z ∧
                    L2NormSq P 0 T X Y Z ≤ ENNReal.ofReal C * (ENNReal.ofReal (x ^ 2) + I0sq P T c)) ∧
            -- (i): a decoupling field whose quotient has the property of h, c₂ replaced by c₃
            (Cond514 c P T ε c₁ c₂ c₃ →
              ∃ u : ℝ≥0 → ℝ → Ω → ℝ,
                IsDecouplingField (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T u ∧
                QuotBound P T u (fun _ q => |q| ≤ c₃)) ∧
            (Cond515 c P T ε c₁ c₂ c₃ →
              ∃ u : ℝ≥0 → ℝ → Ω → ℝ,
                IsDecouplingField (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T u ∧
                QuotBound P T u (fun _ q => c₃⁻¹ ≤ q)) ∧
            (Cond516 c P T ε c₁ c₂ c₃ →
              ∃ u : ℝ≥0 → ℝ → Ω → ℝ,
                IsDecouplingField (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T u ∧
                QuotBound P T u (fun _ q => c₃⁻¹ ≤ q)) ∧
            (Cond517 c P T ε c₁ c₂ c₃ →
              ∃ u : ℝ≥0 → ℝ → Ω → ℝ,
                IsDecouplingField (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T u ∧
                QuotBound P T u (fun _ q => q ≤ -c₃⁻¹)) ∧
            (Cond518 c P T ε c₁ c₂ c₃ →
              ∃ u : ℝ≥0 → ℝ → Ω → ℝ,
                IsDecouplingField (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T u ∧
                QuotBound P T u (fun _ q => q ≤ -c₃⁻¹)) ∧
            (Cond519 c P T ε c₁ c₂ c₃ ∧ SigmaNonzero c P T →
              ∃ u : ℝ≥0 → ℝ → Ω → ℝ,
                IsDecouplingField (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T u ∧
                QuotBound P T u (fun _ q => 0 ≤ q ∧ q ≤ c₃)) ∧
            (Cond520 c P T ε c₁ c₂ c₃ →
              ∃ u : ℝ≥0 → ℝ → Ω → ℝ,
                IsDecouplingField (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T u ∧
                QuotBound P T u (fun _ q => q ≤ c₃)) ∧
            (Cond521 c P T ε c₁ c₂ c₃ ∧ SigmaNonzero c P T →
              ∃ u : ℝ≥0 → ℝ → Ω → ℝ,
                IsDecouplingField (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T u ∧
                QuotBound P T u (fun _ q => -c₃ ≤ q ∧ q ≤ 0)) ∧
            (Cond522 c P T ε c₁ c₂ c₃ →
              ∃ u : ℝ≥0 → ℝ → Ω → ℝ,
                IsDecouplingField (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T u ∧
                QuotBound P T u (fun _ q => -c₃ ≤ q)) := by sorry

end UnifiedFBSDE.Main
