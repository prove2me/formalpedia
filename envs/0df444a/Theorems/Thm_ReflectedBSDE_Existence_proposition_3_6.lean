-- Prove2me | Theorems.Thm_ReflectedBSDE_Existence_proposition_3_6
-- name    : ReflectedBSDE.Existence.proposition_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:22.646977+00:00
-- url     : https://prove2.me/theorems/fc3f7417-a60b-4ca3-9ee5-dbf2eafde0fd
-- title:
--   Proposition 3.6 — stability of the reflected BSDE with respect to $(\xi, f, S)$
-- statement:
--   For every horizon $T$ and Lipschitz constant $K>0$ there is a constant $c$, uniform in the Brownian dimension $d$, with the following property. Let $(\xi,f,S)$ and $(\xi',f',S')$ be two triples satisfying (i)–(iv) with Lipschitz constant $K$, and $S_T\le\xi$, $S'_T\le\xi'$. Let $(Y,Z,K)$ and $(Y',Z',K')$ be square-integrable solutions ((v), (v′), (vi)–(viii)) of the corresponding reflected BSDEs. Put $\Delta\xi=\xi-\xi'$, $\Delta f=f-f'$, $\Delta S=S-S'$, $\Delta Y=Y-Y'$, $\Delta Z=Z-Z'$, $\Delta K=K-K'$. Then
--   $$E\Big(\sup_{0\le t\le T}|\Delta Y_t|^2+\int_0^T|\Delta Z_t|^2dt+|\Delta K_T|^2\Big)\le c\,E\Big(|\Delta\xi|^2+\int_0^T|\Delta f(t,Y_t,Z_t)|^2dt\Big)+c\Big[E\Big(\sup_{0\le t\le T}|\Delta S_t|^2\Big)\Big]^{1/2}\Psi_T^{1/2},$$
--   where
--   $$\Psi_T=E\Big[\xi^2+\int_0^Tf^2(t,0,0)\,dt+\sup_{0\le t\le T}(S_t^+)^2+\xi'^2+\int_0^Tf'^2(t,0,0)\,dt+\sup_{0\le t\le T}(S_t'^+)^2\Big].$$
--
--   The solution depends continuously on the terminal value, the coefficient and the obstacle. With identical data the right side vanishes, which gives uniqueness (Corollary 3.7).
--
--   **Formalization Note** As in Proposition 3.5, $c$ is quantified before the dimension, probability space, data and solutions, and depends only on $(T,K)$; both coefficients share the Lipschitz constant. All quantities lie in $[0,\infty]$, the exponents $1/2$ are real powers there, and $0\cdot\infty=0$. If $E\sup|\Delta S|^2=\infty$ the bound is trivial unless $\Psi_T=0$.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 711 (PDF p. 10), Proposition 3.6

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

universe u

/-- Proposition 3.6 (p. 711): stability. For every `T` and Lipschitz constant `L` there is
a constant `c`, uniform in the Brownian dimension, such that for two data triples `(ξ, f, S)`, `(ξ', f', S')` satisfying (i)–(iv)
with Lipschitz constant `L` and square-integrable solutions `(Y, Z, K)`, `(Y', Z', K')`,
`E(sup|ΔY_t|² + ∫₀ᵀ|ΔZ_t|² dt + |ΔK_T|²) ≤ c E(|Δξ|² + ∫₀ᵀ|Δf(t, Y_t, Z_t)|² dt)
  + c [E(sup|ΔS_t|²)]^{1/2} Ψ_T^{1/2}`. -/
theorem proposition_3_6 :
    ∀ (T : ℝ≥0) (L : ℝ), ∃ c : ℝ≥0,
      ∀ (d : ℕ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
        (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
        (ξ' : Ω → ℝ) (f' : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S' : ℝ≥0 → Ω → ℝ)
        (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
        (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ),
        IsStandardData (augmentedFiltration P hB) P T L ξ f S →
        IsStandardData (augmentedFiltration P hB) P T L ξ' f' S' →
        SatisfiesV (augmentedFiltration P hB) P T Z →
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K →
        SatisfiesVPrime (augmentedFiltration P hB) P T Y K →
        SatisfiesV (augmentedFiltration P hB) P T Z' →
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ' f' S' Y' Z' K' →
        SatisfiesVPrime (augmentedFiltration P hB) P T Y' K' →
        ∫⁻ ω, ((⨆ t ∈ Iic T, ‖Y t ω - Y' t ω‖ₑ ^ 2)
            + (∫⁻ s in Icc (0 : ℝ) T,
                ENNReal.ofReal (euclSq (Z s.toNNReal ω - Z' s.toNNReal ω)))
            + ‖K T ω - K' T ω‖ₑ ^ 2) ∂P
          ≤ (c : ℝ≥0∞) * ∫⁻ ω, (‖ξ ω - ξ' ω‖ₑ ^ 2
              + ∫⁻ s in Icc (0 : ℝ) T,
                ‖f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω)
                  - f' s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω)‖ₑ ^ 2) ∂P
            + (c : ℝ≥0∞) * (supSqMoment P T (fun t ω => S t ω - S' t ω)) ^ (1 / 2 : ℝ)
              * (∫⁻ ω, (‖ξ ω‖ₑ ^ 2
                  + (∫⁻ s in Icc (0 : ℝ) T, ‖f s.toNNReal ω 0 0‖ₑ ^ 2)
                  + (⨆ t ∈ Iic T, ‖max (S t ω) 0‖ₑ ^ 2)
                  + ‖ξ' ω‖ₑ ^ 2
                  + (∫⁻ s in Icc (0 : ℝ) T, ‖f' s.toNNReal ω 0 0‖ₑ ^ 2)
                  + ⨆ t ∈ Iic T, ‖max (S' t ω) 0‖ₑ ^ 2) ∂P) ^ (1 / 2 : ℝ) := by sorry

end ReflectedBSDE.Existence
