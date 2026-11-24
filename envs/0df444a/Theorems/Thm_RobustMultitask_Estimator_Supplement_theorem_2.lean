-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_Supplement_theorem_2
-- name    : RobustMultitask.Estimator.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:58:09.764372+00:00
-- url     : https://prove2.me/theorems/ab73036b-4717-4da3-a539-a4a3ace75dc1
-- title:
--   Theorem 2, p. 18 (corrected: λ includes the target's noise level) — data-poor error bound Õ(s/√nⱼ) of the RMEstimator
-- statement:
--   Consider the fixed-design multitask linear model of §2 with standardized designs, sparse heterogeneity $\|\beta^i-\beta^\dagger\|_0\le s$ and independent mean-zero $\sigma_i$-subgaussian noise. Let $C_0>2$ and $\psi>0$, and put $\zeta=\frac{C_0-2}{4C_0}$. Then there is a constant $K_0>0$, depending only on $C_0$ and $\psi$, with the following property. Let $j$ be a data-poor task such that
--
--   1. (Assumption 2) $\widehat\Sigma^j\in\mathcal C(\bar{\mathcal I}_j,\psi)$, where $\bar{\mathcal I}_j=\mathcal I^\zeta_{\mathrm{well}}\cup\mathcal I_j$;
--   2. (Assumption 1 for the other tasks) $\lambda_{\min}(\widehat\Sigma^i)\ge\psi$ for every $i\ne j$.
--
--   Let $\delta\ge 6d\exp\bigl(-\frac{N-1}9(\frac{C_0-2}{4C_0})^2\bigr)$, and run the data-poor RMEstimator (Remark 4) with
--   $$\lambda=\max_{i\in[N]}\sqrt{32\sigma_i^2\log(4d/\delta)},\quad\lambda_j=\frac\lambda{\sqrt{n_j}},\quad\eta=\sqrt{\frac{9\log(6d/\delta)}{N-1}},\quad\omega=\zeta+\eta .$$
--   Then every output $\widehat\beta^j_{RM}$ satisfies, with probability at least $1-\delta$ and $\bar\sigma=\max_i\sigma_i$,
--   $$\|\widehat\beta^j_{RM}-\beta^j\|_1\le K_0\Bigl(\sqrt{\frac{\bar\sigma^2s^2\log(4d/\delta)}{n_j}}+\max_{i\ne j}\sqrt{\frac{d^2\sigma_i^2\log N}{n_i}}+\max_{i\ne j}\sqrt{\frac{d^2\sigma_i^2\log N\log(6d/\delta)}{Nn_i}}\Bigr).$$
--
--   In the data-poor regime $n_j=\Theta(n_i/d^2)$ for $i\ne j$, with bounded noise levels, the right-hand side is $\tilde O(s/\sqrt{n_j})$: the error depends on the dimension only logarithmically, although $\beta^j$ is dense.
--
--   **Formalization Note** The failure probability bounds the outer measure, so the estimator need not be measurable, and every LASSO minimizer is covered. The constant $K_0$ is chosen before the instance: it does not depend on $N,d,s,n,\sigma$ or $\delta$. The same $\psi$ serves in both assumptions (take the smaller of two constants).
--
--   Differences from the source:
--   - generalization: the rate Õ(s/√nⱼ) in the regime nⱼ = Θ(nᵢ/d²) → the three-term bound of the proof (p. 44), with a constant depending only on C₀ and ψ, on every sample-size profile; reason: under nⱼ ≥ nᵢ/(c d²) and bounded σᵢ each term is at most a constant times s√(log(4d/δ) log N/nⱼ) or that rate with its logarithms, which is the source's Õ(s/√nⱼ)
--   - correction: λ = max_{i≠j} √(32σᵢ² log(4d/δ)) (A.3, p. 43) → λ = max_{i∈[N]} √(32σᵢ² log(4d/δ)); reason: the target's noise event (Lemma 1) has probability 1 − 2d exp(−λⱼ²nⱼ/(32σⱼ²)), which is at least 1 − δ/2 only if λ ≥ √(32σⱼ² log(4d/δ)), and the proof on p. 44 writes σⱼ in the first term; the two rules coincide whenever σⱼ ≤ max_{i≠j} σᵢ, and Theorem 2 asks only for "appropriate choices" of λ
--   - encoding: the numerical constants of p. 44 → an existential constant K₀ depending only on C₀ and ψ; reason: the theorem is an Õ statement, and the coefficients on p. 44 come from Proposition 8, whose proof drops a nonnegative term from (22) and counts N rather than N − 1 donors
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 18, Theorem 2 (Definition 3, Assumption 2, Remark 4); hyperparameters p. 43 (Appendix A.3); proof p. 44

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean
import Definitions.Def_RobustMultitask_Estimator_Model
import Definitions.Def_RobustMultitask_Estimator_Algorithm
import Definitions.Def_RobustMultitask_Estimator_Alignment
import Definitions.Def_RobustMultitask_Estimator_Supplement_DataPoor

namespace RobustMultitask.Estimator.Supplement

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Theorem 2, p. 18, with the data-poor variant of Algorithm 1 (Remark 4) and the
hyperparameters of Appendix A.3 (p. 43), the regularization level taken over all tasks
(see the Formalization Note). For every `C₀ > 2` and `ψ > 0` there is a constant `K₀`
(depending only on `C₀` and `ψ`) such that: in the fixed-design multitask model, if the
data-poor task `j` satisfies Assumption 2 (`Σ̂ʲ ∈ C(ℐ̄ⱼ, ψ)` with `ζ = (C₀−2)/(4C₀)`) and every
other task satisfies `λ_min(Σ̂ⁱ) ≥ ψ`, then for every `δ ≥ exp(−((N−1)/9)((C₀−2)/(4C₀))² +
log(6d))`, with `λ = max_i √(32σ_i² log(4d/δ))`, `λ_j = λ/√n_j`, `η = √(9 log(6d/δ)/(N−1))`,
`ω = ζ + η`, every output `β̂ʲ_RM` satisfies with probability at least `1 − δ`
`‖β̂ʲ_RM − βʲ‖₁ ≤ K₀ ( √(σ̄² s² log(4d/δ)/n_j) + max_{i≠j} √(d²σ_i² log N/n_i)
  + max_{i≠j} √(d²σ_i² log N log(6d/δ)/(N n_i)) )`. -/
theorem theorem_2 (C₀ ψ : ℝ) (hC₀ : 2 < C₀) (hψ : 0 < ψ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {N d : ℕ} (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
        (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
        (ε : (j : Fin N) → Fin (n j) → Ω → ℝ),
        IsMultitaskModel P n X β βdag s σ ε →
        ∀ (j : Fin N),
        sampleCov (X j) ∈ CompatSet (augSupport β βdag ((C₀ - 2) / (4 * C₀)) j) ψ →
        (∀ i, i ≠ j → MinEigAtLeast (sampleCov (X i)) ψ) →
        ∀ (δ : ℝ),
        6 * (d : ℝ) * Real.exp (-(((N : ℝ) - 1) * ((C₀ - 2) / (4 * C₀)) ^ 2) / 9) ≤ δ →
        ∀ (η lam : ℝ),
        η = Real.sqrt (9 * Real.log (6 * d / δ) / ((N : ℝ) - 1)) →
        lam = (⨆ i, Real.sqrt (32 * (σ i : ℝ) ^ 2 * Real.log (4 * d / δ))) / Real.sqrt (n j) →
        ∀ (βhat : Ω → Fin d → ℝ),
        (∀ ω, IsDataPoorRMEstimate n X (fun k => response X β ε k ω)
          ((C₀ - 2) / (4 * C₀) + η) lam j (βhat ω)) →
        P {ω | K₀ * (Real.sqrt ((⨆ i, (σ i : ℝ)) ^ 2 * (s : ℝ) ^ 2 * Real.log (4 * d / δ) / n j)
                + (⨆ i : {i // i ≠ j},
                    Real.sqrt ((d : ℝ) ^ 2 * (σ i : ℝ) ^ 2 * Real.log N / n i))
                + (⨆ i : {i // i ≠ j},
                    Real.sqrt ((d : ℝ) ^ 2 * (σ i : ℝ) ^ 2 * Real.log N * Real.log (6 * d / δ)
                      / (N * n i))))
              < l1 (βhat ω - β j)}
          ≤ ENNReal.ofReal δ := by sorry

end RobustMultitask.Estimator.Supplement
