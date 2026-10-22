-- Prove2me | Theorems.Thm_SimpleCorrMFG_Conv_lemma_A_3
-- name    : SimpleCorrMFG.Conv.lemma_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:30.944098+00:00
-- url     : https://prove2.me/theorems/64ce6c3f-2a3f-4cf7-bb2c-5b13d9e20f70
-- title:
--   Lemma A.3, pp. 28–29 — limits in distribution of regular conditional distributions
-- statement:
--   Let $\mathcal Y,\mathcal Z$ be Polish spaces. For each $n$ let $Y_n,Z_n$ be random variables on $(\Omega_n,\mathcal F_n,P_n)$ with values in $\mathcal Y$ and $\mathcal Z$, and let $\kappa_n$ be a regular conditional distribution of $Y_n$ given $\sigma(Z_n)$, inducing a $\mathcal P(\mathcal Y)$-valued random variable. Suppose that $(Y_n,Z_n,\kappa_n)$ converges in distribution to some $\mathcal Y\times\mathcal Z\times\mathcal P(\mathcal Y)$-valued random variable $(Y,Z,\kappa)$ on $(\Omega,\mathcal F,P)$, where $\mathcal P(\mathcal Y)$ carries the topology of weak convergence. Then for every $A\in\mathcal B(\mathcal Y)$ and $B\in\mathcal B(\mathcal Z)$,
--   $$P(Y\in A,\ Z\in B)=\mathbb E\big[\mathbf 1_B(Z)\cdot\kappa(A)\big].$$
--   If, in addition, $\kappa(A)$ is $\sigma(Z)$-measurable for every $A\in\mathcal B(\mathcal Y)$, then $\kappa$ is a regular conditional distribution of $Y$ given $\sigma(Z)$.
--
--   In Step Four of the proof of Theorem 6.1 the lemma transports the pre-limit consistency identity to the limit points.
--
--   **Formalization Note** Convergence in distribution of $(Y_n,Z_n,\kappa_n)$ is stated as convergence of $\mathbb E_n[g(Y_n,Z_n,\kappa_n)]$ to $\mathbb E[g(Y,Z,\kappa)]$ for every bounded continuous $g$ on $\mathcal Y\times\mathcal Z\times\mathcal P(\mathcal Y)$, which is the definition of weak convergence of the laws. This avoids fixing a σ-algebra on `ProbabilityMeasure 𝒴` other than Mathlib's Giry one, which for Polish $\mathcal Y$ coincides with the Borel σ-algebra of the weak topology. Expectations of $[0,1]$-valued quantities are lower Lebesgue integrals.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, pp. 28–29, Lemma A.3 (setting of κ_n on p. 28; standing assumptions of Appendix A, p. 27)

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_RegCondDistrib

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- Lemma A.3 (pp. 28–29). Convergence in distribution of `(Y_n, Z_n, κ_n)` to `(Y, Z, κ)` in
`𝒴 × 𝒵 × P(𝒴)` (weak topology on `P(𝒴)`) is stated through bounded continuous test functions. -/
theorem lemma_A_3 {𝒴 𝒵 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    [TopologicalSpace 𝒵] [PolishSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (Yn : ∀ n, Ω n → 𝒴) (Zn : ∀ n, Ω n → 𝒵) (κn : ∀ n, Ω n → ProbabilityMeasure 𝒴)
    (hYn : ∀ n, Measurable (Yn n)) (hZn : ∀ n, Measurable (Zn n)) (hκn : ∀ n, Measurable (κn n))
    (hrcd : ∀ n, IsRegCondDistrib (P n) (Yn n) (fun ω => (κn n ω : Measure 𝒴))
      (MeasurableSpace.comap (Zn n) inferInstance))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → 𝒴) (Z : Ω' → 𝒵) (κ : Ω' → ProbabilityMeasure 𝒴) (hY : Measurable Y)
    (hZ : Measurable Z) (hκ : Measurable κ)
    (hconv : ∀ g : BoundedContinuousFunction (𝒴 × 𝒵 × ProbabilityMeasure 𝒴) ℝ,
      Tendsto (fun n => ∫ ω, g (Yn n ω, Zn n ω, κn n ω) ∂(P n)) atTop
        (𝓝 (∫ ω, g (Y ω, Z ω, κ ω) ∂P'))) :
    (∀ A : Set 𝒴, MeasurableSet A → ∀ B : Set 𝒵, MeasurableSet B →
        P' (Y ⁻¹' A ∩ Z ⁻¹' B) = ∫⁻ ω in Z ⁻¹' B, (κ ω : Measure 𝒴) A ∂P') ∧
      ((∀ A : Set 𝒴, MeasurableSet A →
          Measurable[MeasurableSpace.comap Z inferInstance] (fun ω => (κ ω : Measure 𝒴) A)) →
        IsRegCondDistrib P' Y (fun ω => (κ ω : Measure 𝒴)) (MeasurableSpace.comap Z inferInstance)) := by sorry

end SimpleCorrMFG.Conv
