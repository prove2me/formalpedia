-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_Supplement_theorem_1
-- name    : RobustMultitask.Estimator.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:57:11.747408+00:00
-- url     : https://prove2.me/theorems/c9999751-cb8c-4e24-9104-7189a2d63100
-- title:
--   Theorem 1, p. 17 (corrected: σ̄ in the first term, envelope constants of 4C₀) — standard-regime error bound of the RMEstimator
-- statement:
--   Consider the fixed-design multitask linear model of §2: $N$ tasks, task $i$ with $n_i$ standardized observations $Y^i=X^i\beta^i+\varepsilon^i$, $\beta^i=\beta^\dagger+\delta^i$ with $\|\delta^i\|_0\le s$, and mutually independent mean-zero $\sigma_i$-subgaussian noise. Assume Assumption 1: $\lambda_{\min}(\widehat\Sigma^i)\ge\psi>0$ for every task. Let $C_0>2$, $s\ge1$, and write $\bar\sigma=\max_i\sigma_i$. Fix a task $j$ and
--   $$\delta\ \ge\ 6d\,\exp\Bigl(-\frac N9\Bigl(\frac{C_0-2}{4C_0}\Bigr)^2\Bigr).$$
--   Run Algorithm 1 with the hyperparameters of Appendix A.2:
--   $$\lambda=\max_{i\in[N]}\sqrt{32\sigma_i^2\log(4d/\delta)},\quad \lambda_j=\frac{\lambda}{\sqrt{n_j}},\quad \zeta=\frac{C_0-2}{4C_0}\sqrt{\frac{\min(s,d)}{d}},\quad \eta=\sqrt{\frac{9\log(6d/\delta)}{N}},\quad \omega=\zeta+\eta .$$
--   Then every output $\widehat\beta^j_{RM}$ satisfies, with probability at least $1-\delta$,
--   $$\|\widehat\beta^j_{RM}-\beta^j\|_1\le\frac{96C_0}{(C_0-2)\psi}\sqrt{\frac{2\bar\sigma^2sd\log(4d/\delta)}{n_j}}+3C_0\max_{i\in[N]}\sqrt{\frac{\sigma_i^2sd\log N}{\psi n_i}}+48C_0\,d\max_{i\in[N]}\sqrt{\frac{\sigma_i^2\log N\log(6d/\delta)}{\psi Nn_i}} .$$
--
--   When the sample sizes are comparable ($n_j\le c\,n_i$ for all $i$, the standard regime) and the noise levels are bounded, the right-hand side is $\tilde O(\sqrt{sd/n_j}+d/\sqrt{Nn_j})$, which is the rate of Theorem 1. With $N=\Omega(d/s)$ tasks this improves the $O(d/\sqrt{n_j})$ error of per-task OLS by a factor $\sqrt d$.
--
--   **Formalization Note** "With probability at least $1-\delta$" is stated as an upper bound on the outer measure of the failure set, so no measurability of the estimator is needed; every LASSO minimizer is covered. Maxima over tasks are suprema over the finite index set.
--
--   Differences from the source:
--   - generalization: the rate Õ(√(sd/nⱼ) + d/√(Nnⱼ)) in the standard regime nⱼ = Θ(nᵢ) → the explicit three-term envelope of the proof (p. 43), with the task-dependent nᵢ and σᵢ, on every sample-size profile; reason: under nⱼ ≤ c nᵢ and bounded σᵢ the envelope is at most a constant times √(sd log(4d/δ)/nⱼ) + √(sd log N/nⱼ) + d√(log N log(6d/δ)/(Nnⱼ)), the source's rate with its logarithms
--   - correction: the first term of p. 43 has σⱼ² → it has σ̄² = maxᵢ σᵢ²; reason: with the A.2 choice λ = maxᵢ √(32σᵢ² log(4d/δ)), the term 6λⱼs/(ζψ) of Proposition 5 equals 96C₀/((C₀−2)ψ)·√(2σ̄² sd log(4d/δ)/nⱼ); σⱼ² is correct only when task j is the noisiest
--   - correction: envelope coefficients 3C₀/4 and 12C₀ (p. 43) → 3C₀ and 48C₀; reason: they come from Proposition 5, whose proof (p. 43) gives the coefficient 4C₀ on its second term, as in the published goal; the rate is unchanged
--   - reading: ζ = ((C₀−2)/(4C₀))√(s/d) → ζ = ((C₀−2)/(4C₀))√(min(s,d)/d); reason: a sparsity bound s > d says no more than s = d, and the source's admissibility check (p. 43, "1 − ½√(s/d)") presumes s ≤ d; the two agree whenever s ≤ d
--   - encoding: s ∈ ℕ → s ≥ 1; reason: the prescribed ζ is positive only for s ≥ 1, and an instance with s = 0 is also an instance with s = 1
--   - encoding: δ in the source's range with δ ≤ 1 used in the proof → every δ above the threshold; reason: for δ ≥ 1 the claim holds trivially, so no hypothesis δ ≤ 1 is needed
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 17, Theorem 1; hyperparameters p. 41 (Appendix A.2); proof and envelope p. 43

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean
import Definitions.Def_RobustMultitask_Estimator_Model
import Definitions.Def_RobustMultitask_Estimator_Algorithm

namespace RobustMultitask.Estimator.Supplement

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Theorem 1, p. 17, with the hyperparameters of Appendix A.2 (p. 41) and the explicit envelope
of its proof (p. 43). In the fixed-design multitask model under Assumption 1, let `C₀ > 2`,
`s ≥ 1`, and `δ ≥ exp(−(N/9)((C₀−2)/(4C₀))² + log(6d))`. With
`λ = max_i √(32σ_i² log(4d/δ))`, `λ_j = λ/√n_j`, `ζ = ((C₀−2)/(4C₀))√(min(s,d)/d)`,
`η = √(9 log(6d/δ)/N)` and `ω = ζ + η`, every output `β̂ʲ_RM` of Algorithm 1 satisfies, with
probability at least `1 − δ`,
`‖β̂ʲ_RM − βʲ‖₁ ≤ 96C₀/((C₀−2)ψ) √(2σ̄² s d log(4d/δ)/n_j)
  + 3C₀ max_i √(σ_i² s d log N/(ψ n_i)) + 48C₀ d max_i √(σ_i² log N log(6d/δ)/(ψ N n_i))`,
`σ̄ = max_i σ_i`. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (ε : (j : Fin N) → Fin (n j) → Ω → ℝ)
    (hmodel : IsMultitaskModel P n X β βdag s σ ε) (ψ : ℝ) (hA1 : Assumption1 n X ψ)
    (C₀ : ℝ) (hC₀ : 2 < C₀) (hs : 1 ≤ s) (j : Fin N) (δ : ℝ)
    (hδ : 6 * (d : ℝ) * Real.exp (-((N : ℝ) * ((C₀ - 2) / (4 * C₀)) ^ 2) / 9) ≤ δ)
    (ζ η lam : ℝ)
    (hζ : ζ = (C₀ - 2) / (4 * C₀) * Real.sqrt ((min s d : ℕ) / (d : ℝ)))
    (hη : η = Real.sqrt (9 * Real.log (6 * d / δ) / N))
    (hlam : lam = (⨆ i, Real.sqrt (32 * (σ i : ℝ) ^ 2 * Real.log (4 * d / δ)))
      / Real.sqrt (n j))
    (βhat : Ω → Fin d → ℝ)
    (hβhat : ∀ ω, IsRMEstimate n X (fun k => response X β ε k ω) (ζ + η) lam j (βhat ω)) :
    P {ω | 96 * C₀ / ((C₀ - 2) * ψ)
            * Real.sqrt (2 * (⨆ i, (σ i : ℝ)) ^ 2 * s * d * Real.log (4 * d / δ) / n j)
          + 3 * C₀ * (⨆ i, Real.sqrt ((σ i : ℝ) ^ 2 * s * d * Real.log N / (ψ * n i)))
          + 48 * C₀ * d * (⨆ i, Real.sqrt ((σ i : ℝ) ^ 2 * Real.log N * Real.log (6 * d / δ)
              / (ψ * N * n i)))
          < l1 (βhat ω - β j)}
      ≤ ENNReal.ofReal δ := by sorry

end RobustMultitask.Estimator.Supplement
