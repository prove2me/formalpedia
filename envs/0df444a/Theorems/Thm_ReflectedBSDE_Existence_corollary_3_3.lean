-- Prove2me | Theorems.Thm_ReflectedBSDE_Existence_corollary_3_3
-- name    : ReflectedBSDE.Existence.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:56.636306+00:00
-- url     : https://prove2.me/theorems/1ae3272d-b4bb-454a-9a7c-a94019a010fc
-- title:
--   Corollary 3.3 (α) — (v) implies (v′): $Z\in\mathbb H^2$ gives $Y\in\mathcal S^2$, $K_T\in\mathbb L^2$
-- statement:
--   Let $(\xi,f,S)$ satisfy (i)–(iv) and $S_T\le\xi$. Let $(Y,Z,K)$ be a solution of the reflected BSDE satisfying (vi)–(viii) together with the integrability assumption (v) on $Z$, namely $E\int_0^T|Z_t|^2\,dt<\infty$. Then condition (v′) holds:
--   $$E\Big[\sup_{0\le t\le T}Y_t^2+K_T^2\Big]<\infty,$$
--   that is, $Y\in\mathcal S^2$ and $K_T\in\mathbb L^2$.
--
--   Square integrability of $Z$ alone controls the whole solution. This is why uniqueness (Corollary 3.7) and existence (Theorem 5.2) need only assume (v).
--
--   **Formalization Note** The paper prints "$Y\in\mathbb H^2$". The displayed condition $E[\sup_tY_t^2]<\infty$ is membership in $\mathcal S^2$, which is what is formalized. Part (β) of the corollary (the stochastic integral $\int_0^t(Y_sZ_s,dB_s)$ is a uniformly integrable martingale) is not formalized: its integrand need not be in $\mathbb H^2$, so it lies outside the $L^2$ Itô integral used here.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 708 (PDF p. 7), Corollary 3.3 (α)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

/-- Corollary 3.3 (α) (p. 708): a solution of (vi)–(viii) with `Z ∈ ℍ²` satisfies (v′):
`E[sup_{0≤t≤T} Y_t² + K_T²] < ∞`, i.e. `Y ∈ 𝒮²` and `K_T ∈ 𝕃²`. -/
theorem corollary_3_3 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (L : ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : IsStandardData (augmentedFiltration P hB) P T L ξ f S)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (hsol : SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K)
    (hZ : SatisfiesV (augmentedFiltration P hB) P T Z) :
    SatisfiesVPrime (augmentedFiltration P hB) P T Y K := by sorry

end ReflectedBSDE.Existence
