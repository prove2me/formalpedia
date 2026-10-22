-- Prove2me | Theorems.Thm_RiskFunctionals_Kusuoka_covariance_coupling
-- name    : RiskFunctionals.Kusuoka.covariance_coupling
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:57.568653+00:00
-- url     : https://prove2.me/theorems/653f5cb7-6e9b-40a0-95df-d1371c1a5573
-- title:
--   Proposition 1.8 — comonotone coupling maximizes, antimonotone coupling minimizes the covariance
-- statement:
--   Let $Y^{(1)},Y^{(2)}$ be square-integrable random variables on a probability space $(\Omega,\mathcal F,\mathbb P)$ with marginal distribution functions $G_1(u)=\mathbb P\{Y^{(1)}\le u\}$ and $G_2(v)=\mathbb P\{Y^{(2)}\le v\}$. Let $(X^{(1)},X^{(2)})$ be any pair on a probability space $(\Omega',\mathcal F',\mathbb P')$ with the same marginals: $X^{(1)}\overset d=Y^{(1)}$, $X^{(2)}\overset d=Y^{(2)}$. Write $\mathrm{Cov}(U,V)=\mathbb E(UV)-\mathbb E U\,\mathbb E V$.
--
--   1. If $(Y^{(1)},Y^{(2)})$ is comonotone coupled, i.e. $\mathbb P\{Y^{(1)}\le u,Y^{(2)}\le v\}=\min(G_1(u),G_2(v))$ for all $u,v$ (1.11), then
--   $$\mathrm{Cov}(X^{(1)},X^{(2)})\le\mathrm{Cov}(Y^{(1)},Y^{(2)}).$$
--   2. If $(Y^{(1)},Y^{(2)})$ is antimonotone coupled, i.e. $\mathbb P\{Y^{(1)}\le u,Y^{(2)}\le v\}=\max(G_1(u)+G_2(v)-1,0)$ for all $u,v$ (1.12), then
--   $$\mathrm{Cov}(Y^{(1)},Y^{(2)})\le\mathrm{Cov}(X^{(1)},X^{(2)}).$$
--
--   In words: for given marginals the covariance is maximized by the comonotone and minimized by the antimonotone coupling. In the proof of the Kusuoka representation this is the step that replaces $\inf\mathbb E(YZ)$ over all couplings by the antimonotone value $\int_0^1F^{-1}(u)G^{-1}(1-u)\,du$.
--
--   **Formalization Note** The book speaks of "the covariance" without stating moment conditions; square integrability of $Y^{(1)},Y^{(2)}$ (hence of $X^{(1)},X^{(2)}$, which have the same laws) is assumed so that every covariance is a finite number. The competing coupling may live on a different probability space, so the statement compares all joint distributions with the given marginals.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 11, Proposition 1.8 (with (1.11), (1.12) on pp. 8–9)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace RiskFunctionals.Kusuoka

/-- Pflug & Römisch, p. 11, Proposition 1.8: among all couplings of two given marginals
`G₁, G₂`, the covariance is largest for the comonotone coupling (1.11)
`ℙ{Y⁽¹⁾ ≤ u, Y⁽²⁾ ≤ v} = min(G₁(u), G₂(v))` and smallest for the antimonotone coupling (1.12)
`ℙ{Y⁽¹⁾ ≤ u, Y⁽²⁾ ≤ v} = max(G₁(u) + G₂(v) − 1, 0)`. The competing coupling `(X₁, X₂)` may live
on another probability space. Covariances are `𝔼(Y⁽¹⁾Y⁽²⁾) − 𝔼Y⁽¹⁾ 𝔼Y⁽²⁾` of square-integrable
variables. -/
theorem covariance_coupling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P']
    (Y₁ Y₂ : Ω → ℝ) (hY₁ : MemLp Y₁ 2 P) (hY₂ : MemLp Y₂ 2 P)
    (X₁ X₂ : Ω' → ℝ) (h₁ : IdentDistrib X₁ Y₁ P' P) (h₂ : IdentDistrib X₂ Y₂ P' P) :
    ((∀ u v : ℝ, P.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
          min (P.real {ω | Y₁ ω ≤ u}) (P.real {ω | Y₂ ω ≤ v})) →
        (∫ ω, X₁ ω * X₂ ω ∂P') - (∫ ω, X₁ ω ∂P') * (∫ ω, X₂ ω ∂P') ≤
          (∫ ω, Y₁ ω * Y₂ ω ∂P) - (∫ ω, Y₁ ω ∂P) * (∫ ω, Y₂ ω ∂P)) ∧
    ((∀ u v : ℝ, P.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
          max (P.real {ω | Y₁ ω ≤ u} + P.real {ω | Y₂ ω ≤ v} - 1) 0) →
        (∫ ω, Y₁ ω * Y₂ ω ∂P) - (∫ ω, Y₁ ω ∂P) * (∫ ω, Y₂ ω ∂P) ≤
          (∫ ω, X₁ ω * X₂ ω ∂P') - (∫ ω, X₁ ω ∂P') * (∫ ω, X₂ ω ∂P')) := by sorry

end RiskFunctionals.Kusuoka
