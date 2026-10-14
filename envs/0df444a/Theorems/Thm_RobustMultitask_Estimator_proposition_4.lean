-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_proposition_4
-- name    : RobustMultitask.Estimator.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:52.606804+00:00
-- url     : https://prove2.me/theorems/139a525f-39b8-443e-8e24-f62016ea59bf
-- title:
--   Proposition 4, p. 16 — trimmed mean of N samples, ζN arbitrarily corrupted: |µ̂ − µ| ≥ C₀ max σⱼ (3ζ+4η)√log(3/η) w.p. ≤ 3exp(−Nη²/9)
-- statement:
--   Let $Z_1,\dots,Z_N$ be random variables on a probability space and $\mathcal J\subseteq[N]$ a set of indices with $|\mathcal J|<\zeta N$, where $0<\zeta<1/2$. Suppose that the samples $\{Z_j\}_{j\in\mathcal J^c}$ are independent and that each $Z_j$, $j\in\mathcal J^c$, is $\sigma_j$-subgaussian with mean $\mu$ (Definition 1), $\sigma_j>0$; the samples $\{Z_j\}_{j\in\mathcal J}$ may be arbitrarily corrupted. Let $\widehat\mu=\mathrm{TrimmedMean}(\{Z_j\}_{j\in[N]},\omega)$ with $\omega=\zeta+\eta$. Then for every constant $C_0>2$ and every $0<\eta\le 1/2-1/C_0-\zeta$,
--   $$\mathbb P\Big[\,|\widehat\mu-\mu|\ \ge\ C_0\max_{j\in\mathcal J^c}\sigma_j\,(3\zeta+4\eta)\sqrt{\log(3/\eta)}\,\Big]\ \le\ 3\exp\Big(-\frac{N\eta^2}{9}\Big).$$
--
--   This is the robust-statistics step of the paper: unlike the classical results, the uncorrupted samples need only be independent, not identically distributed, so the bound applies to per-task least-squares estimates with different variances.
--
--   **Formalization Note** The corrupted samples $Z_j$, $j\in\mathcal J$, are arbitrary functions of the sample point: no independence, measurability or integrability is assumed. Definition 1 is Mathlib's `HasSubgaussianMGF (Z j − µ) (σ j ^ 2)` (written with `mu`), which forces $\mathbb E[Z_j]=\mu$. Independence is `iIndepFun` over the subtype $\mathcal J^c$. The constant $C_0$ is universally quantified ("with some constant $C_0>2$" holds for every such $C_0$ in the proof, p. 40), and the trimming level is fixed to $\omega=\zeta+\eta$. The probability is the outer measure of the failure event, so no measurability of the trimmed mean is needed. The maximum over $\mathcal J^c$ is a supremum over that (nonempty, since $|\mathcal J|<N/2$) subtype. The trimmed mean removes $\lfloor N\omega\rfloor$ values from each end. The hypothesis $\sigma_j>0$ is added: with all $\sigma_j=0$ the threshold is $0$ and the event "$\ge 0$" is certain, so the printed inequality would fail.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 16, Proposition 4 (proof pp. 39–40)

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean

namespace RobustMultitask.Estimator

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Proposition 4, p. 16 (trimmed mean under corruption). `N` samples `Z j`; a set `𝒥` of
corrupted indices with `|𝒥| < ζN`, `0 < ζ < 1/2`. The uncorrupted samples `Z j`, `j ∉ 𝒥`, are
independent, `σ_j`-subgaussian about the common mean `µ` (written `mu`; `σ_j > 0`); the corrupted ones are
arbitrary functions of the sample point. Then for every `C₀ > 2` and `0 < η ≤ 1/2 − 1/C₀ − ζ`,
with `µ̂ = TrimmedMean({Z_j}, ω)` and `ω = ζ + η`,
`P[|µ̂ − µ| ≥ C₀ max_{j∈𝒥ᶜ} σ_j (3ζ + 4η) √log(3/η)] ≤ 3 exp(−Nη²/9)`. -/
theorem proposition_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (Z : Fin N → Ω → ℝ) (𝒥 : Finset (Fin N)) (σ : Fin N → ℝ≥0) (mu ζ η C₀ : ℝ)
    (hC₀ : 2 < C₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hcard : (𝒥.card : ℝ) < ζ * N)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2 - 1 / C₀ - ζ)
    (hσ : ∀ j ∉ 𝒥, 0 < σ j)
    (hsub : ∀ j ∉ 𝒥, HasSubgaussianMGF (fun ω => Z j ω - mu) (σ j ^ 2) P)
    (hind : iIndepFun (fun j : {j : Fin N // j ∉ 𝒥} => Z j) P) :
    P {ω | C₀ * (⨆ j : {j : Fin N // j ∉ 𝒥}, (σ j : ℝ)) * (3 * ζ + 4 * η)
            * Real.sqrt (Real.log (3 / η))
          ≤ |trimmedMean (fun j => Z j ω) (ζ + η) - mu|}
      ≤ ENNReal.ofReal (3 * Real.exp (-((N : ℝ) * η ^ 2) / 9)) := by sorry

end RobustMultitask.Estimator
