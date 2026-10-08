-- Prove2me | Theorems.Thm_ReflectedBSDE_Existence_proposition_2_2
-- name    : ReflectedBSDE.Existence.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:49.207108+00:00
-- url     : https://prove2.me/theorems/89a511af-c819-4f0c-8482-dbff24a75d62
-- title:
--   Proposition 2.2 — $K_T-K_t$ is a running supremum of the negative part
-- statement:
--   Let $(\xi,f,S)$ satisfy (i)–(iv) and $S_T\le\xi$, and let $(Y,Z,K)$ satisfy (vi)–(viii) of the reflected BSDE with stochastic integrals $J^j_t=\int_0^tZ^j_s\,dB^j_s$. Then almost surely, for every $t\in[0,T]$,
--   $$K_T-K_t=\sup_{t\le u\le T}\Big(\xi+\int_u^Tf(s,Y_s,Z_s)\,ds-\int_u^T(Z_s,dB_s)-S_u\Big)^-,$$
--   where $\int_u^T(Z_s,dB_s)=\sum_j(J^j_T-J^j_u)$ and $a^-=\max(-a,0)$.
--
--   The proposition comes from the Skorohod lemma applied in reversed time. It writes the reflecting process in terms of the other components of the solution, and it is the starting point of the integrability estimates for $K$.
--
--   **Formalization Note** Because the Itô integral is only defined for square-integrable integrands, the hypothesis "(vi)–(viii)" contains $Z\in\mathbb H^2$, condition (v), which the paper does not assume here (recorded deviation). The identity is stated almost surely for all $t$ at once, which implies the paper's "for each $t$". It is stated for the solution's own continuous version $J$ of the stochastic integrals. The supremum is a real supremum over the compact interval $[t,T]$, which is finite almost surely because the expression is continuous in $u$.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 705 (PDF p. 4), Proposition 2.2, (1)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

/-- Proposition 2.2 (p. 705): for a solution of (vi)–(viii), almost surely, for every
`t ∈ [0, T]`,
`K_T − K_t = sup_{t≤u≤T} (ξ + ∫ᵤᵀ f(s, Y_s, Z_s) ds − ∫ᵤᵀ (Z_s, dB_s) − S_u)⁻`,
where `∫ᵤᵀ (Z_s, dB_s) = Σⱼ (Jʲ_T − Jʲ_u)` for the stochastic integrals `J` of the solution. -/
theorem proposition_2_2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (L : ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : IsStandardData (augmentedFiltration P hB) P T L ξ f S)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (J : Fin d → ℝ≥0 → Ω → ℝ)
    (hsol : SolvesRBSDEWith (augmentedFiltration P hB) P T B ξ f S Y Z K J) :
    ∀ᵐ ω ∂P, ∀ t ≤ T,
      K T ω - K t ω = ⨆ u : Icc t T,
        max (-(ξ ω
          + (∫ s in Icc ((u : ℝ≥0) : ℝ) T, f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω))
          - ∑ j, (J j T ω - J j u ω) - S u ω)) 0 := by sorry

end ReflectedBSDE.Existence
