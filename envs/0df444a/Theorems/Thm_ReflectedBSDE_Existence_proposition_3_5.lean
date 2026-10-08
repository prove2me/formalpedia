-- Prove2me | Theorems.Thm_ReflectedBSDE_Existence_proposition_3_5
-- name    : ReflectedBSDE.Existence.proposition_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:02.96733+00:00
-- url     : https://prove2.me/theorems/0f7a7f83-67ee-44ad-9552-bec1e80693b2
-- title:
--   Proposition 3.5 — a priori estimate $E(\sup Y^2+\int|Z|^2+K_T^2)\le C\,E(\xi^2+\int f^2(t,0,0)+\sup(S^+)^2)$
-- statement:
--   For every horizon $T$ and Lipschitz constant $K>0$ there is a constant $C$, uniform in the Brownian dimension $d$, with the following property. Let $(\xi,f,S)$ satisfy (i)–(iv) with Lipschitz constant $K$, and $S_T\le\xi$. Let $(Y,Z,K)$ be a square-integrable solution of the reflected BSDE, i.e. one satisfying (v), (v′) and (vi)–(viii). Then
--   $$E\Big(\sup_{0\le t\le T}Y_t^2+\int_0^T|Z_t|^2\,dt+K_T^2\Big)\le C\,E\Big(\xi^2+\int_0^Tf^2(t,0,0)\,dt+\sup_{0\le t\le T}(S_t^+)^2\Big).$$
--
--   The estimate bounds the size of the solution by the size of the data. It is the basic tool for the contraction argument behind existence and for the stability estimate (Proposition 3.6).
--
--   **Formalization Note** The paper says "there exists a constant $C$" after fixing a solution. Read that way the statement is trivial, since the left side is finite. Its proof gives a constant that depends only on the Lipschitz constant and $T$, so the formal statement puts $\exists C$ before the dimension, probability space, data and solution. Expectations are lower Lebesgue integrals in $[0,\infty]$. $|Z|$ is the Euclidean norm, and the Lipschitz constant is called `L` in Lean.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 709 (PDF p. 8), Proposition 3.5

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

/-- Proposition 3.5 (p. 709): a priori estimate. For every dimension `d`, horizon `T` and
Lipschitz constant `L` there is a constant `C`, uniform in the Brownian dimension, such that every square-integrable solution
`(Y, Z, K)` (conditions (v)–(viii) and (v′)) of the RBSDE with data `(ξ, f, S)` satisfying
(i)–(iv) with Lipschitz constant `L` obeys
`E(sup_{0≤t≤T} Y_t² + ∫₀ᵀ |Z_t|² dt + K_T²) ≤ C E(ξ² + ∫₀ᵀ f²(t, 0, 0) dt + sup_{0≤t≤T} (S_t⁺)²)`. -/
theorem proposition_3_5 :
    ∀ (T : ℝ≥0) (L : ℝ), ∃ C : ℝ≥0,
      ∀ (d : ℕ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
        (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
        (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ),
        IsStandardData (augmentedFiltration P hB) P T L ξ f S →
        SatisfiesV (augmentedFiltration P hB) P T Z →
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K →
        SatisfiesVPrime (augmentedFiltration P hB) P T Y K →
        ∫⁻ ω, ((⨆ t ∈ Iic T, ‖Y t ω‖ₑ ^ 2)
            + (∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (euclSq (Z s.toNNReal ω)))
            + ‖K T ω‖ₑ ^ 2) ∂P
          ≤ (C : ℝ≥0∞) * ∫⁻ ω, (‖ξ ω‖ₑ ^ 2
            + (∫⁻ s in Icc (0 : ℝ) T, ‖f s.toNNReal ω 0 0‖ₑ ^ 2)
            + ⨆ t ∈ Iic T, ‖max (S t ω) 0‖ₑ ^ 2) ∂P := by sorry

end ReflectedBSDE.Existence
