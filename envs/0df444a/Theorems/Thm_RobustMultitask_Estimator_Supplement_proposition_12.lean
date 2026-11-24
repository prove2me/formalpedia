-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_Supplement_proposition_12
-- name    : RobustMultitask.Estimator.Supplement.proposition_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:02:47.98425+00:00
-- url     : https://prove2.me/theorems/da2f65b2-685d-4486-9527-32016c2dcc2f
-- title:
--   Proposition 12, p. 55 (corrected: instance-specific λ₁,₀, d ≥ 2) — all-sample tail bound of RMBandit on the event 𝒜
-- statement:
--   Work in the bandit model of §5 under Assumptions 6–10, with $C_0>2$, $d\ge2$, $s\ge1$, total horizon $H\ge1$, and RMBandit with the hyperparameters, $q$ and constants $C_1,C_2,C_3$ of Appendix D.1 (any LASSO selection rule and tie-breaking rule). Assume the forced admissibility $\eta_0\le\frac12-\frac1{C_0}-\zeta_0$, and let $\mathcal B_m$, $m\ge1$, be a nonempty batch with
--   $$\log(d|\mathcal B_m|)\le\Bigl(\frac12-\frac1{C_0}-\zeta_{1,0}\Bigr)^2\frac{\rho N}9 .$$
--   Then for every instance $j$ and optimal arm $k\in\mathcal K^j_{\mathrm{opt}}$, conditionally on the event $\mathcal A$ of (35),
--   $$\|\widehat\beta^j_{k,\bar m}-\beta^j_k\|_1\le C_1\sqrt{\frac{sd\log(dp_j|\mathcal B_{\bar m}|)}{p_j|\mathcal B_{\bar m}|}}+C_2\sqrt{\frac{sd\log(\rho N)}{p_j|\mathcal B_m|}}+C_3d\sqrt{\frac{\log(dp_j|\mathcal B_m|)\log(\rho N)}{Np_j|\mathcal B_m|}}$$
--   with probability at least
--   $$1-\Bigl(\frac6{\min_{i\in\mathcal W_k}p_i|\mathcal B_m|}+\frac4{p_j|\mathcal B_m|}+\sum_{i\in\mathcal W_k}7d\exp\Bigl(-\frac{p_*p_i\psi|\mathcal B_m|}{32dx_{\max}^2}\Bigr)\Bigr).$$
--
--   Once the forced estimators have screened out the suboptimal arms, the all-sample estimators of the optimal arms converge at the multitask rate; this drives the regret bound of Theorem 3.
--
--   **Formalization Note** "Conditionally on $\mathcal A$" is stated as $\mathbb P(\text{failure}\cap\mathcal A)\le(\text{bound})\cdot\mathbb P(\mathcal A)$ with outer measures, so no measurability is needed; for measurable events it is the conditional statement. $|\mathcal B_m|$ and $|\mathcal B_{\bar m}|$ are the sizes of the batches truncated at $H$.
--
--   Differences from the source:
--   - correction: λ₁,₀ = maxᵢ √(384σᵢ² x²_max/p*) (D.1 display) → the instance-specific λ₁,₀^{(j)} = √(384σⱼ² x²_max/p*); reason: the proof (p. 63) sets λⱼ = √(384σⱼ² x²_max log(d|ℬʲ_m̄|)/(p*|ℬʲ_m̄|)), and C₁ contains σⱼ, not maxᵢ σᵢ; λ₀ is instance-specific as in Proposition 11
--   - correction: no condition on d → d ≥ 2; reason: the proof uses (39) and log(d minᵢ|ℬⁱ_m|) ≥ log d, and the source assumes d > 1 (p. 66); excluded: d = 1
--   - reading: N = Ω(log(d) log(T)) → η₀ ≤ 1/2 − 1/C₀ − ζ₀ and log(d|ℬ_m|) ≤ (1/2 − 1/C₀ − ζ₁,₀)² ρN/9; reason: these are the two requirements the proofs state (pp. 60 and 63)
--   - reading: the batch Step 1 of the all-sample estimator → the trimmed mean over the instances that have samples of arm k in ℬ_m; reason: the proof (p. 62) takes the trimmed mean over 𝒲_k, the instances that pull arm k on 𝒜
--   - reading: "when the event 𝒜 holds … with probability at least" → P(failure ∩ 𝒜) ≤ bound · P(𝒜); reason: the proof bounds the conditional probability given 𝒜 (p. 63)
--   - reading: ζ₁,₀ = ((C₀−2)/(4C₀))√(s/d), |ℬ₀| = q log T → min(s,d) in place of s, s ≥ 1, |ℬ₀| = ⌈q log H⌉; reason: as in Proposition 11
--   - encoding: an arbitrary minimizer and arbitrary ties → arbitrary non-anticipating selection and tie-breaking rules; reason: Algorithm 2 computes its estimators and arms from past data; every rule is covered
--   - encoding: m unspecified → m ≥ 1 with ℬ_m nonempty, H ≥ 1; reason: the all-sample estimator is updated at the end of batches m ≥ 1, and an empty batch makes the bound undefined
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 55, Proposition 12 and (35); parameters p. 56 (Appendix D.1); proof pp. 60–63

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean
import Definitions.Def_RobustMultitask_Estimator_Algorithm
import Definitions.Def_RobustMultitask_Estimator_Supplement_DataPoor
import Definitions.Def_RobustMultitask_Estimator_Supplement_BanditModel
import Definitions.Def_RobustMultitask_Estimator_Supplement_BanditAlgorithm
import Definitions.Def_RobustMultitask_Estimator_Supplement_BanditTuning

namespace RobustMultitask.Estimator.Supplement

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Proposition 12, p. 55 (proof pp. 60–63), with the hyperparameters, `q` and constants
`C₁, C₂, C₃` of Appendix D.1. Under the bandit model and Assumptions 6–10, for `C₀ > 2`, `d ≥ 2`,
`s ≥ 1`, total horizon `H ≥ 1`, the forced-stage admissibility `η₀ ≤ 1/2 − 1/C₀ − ζ₀` and, for a
batch `B_m` (`m ≥ 1`, nonempty), the all-sample admissibility
`log(d|B_m|) ≤ (1/2 − 1/C₀ − ζ_{1,0})² ρN/9`, the all-sample estimator of every optimal arm
`k ∈ 𝒦ʲ_opt` computed by RMBandit satisfies, conditionally on the event `A` of (35),
`‖β̂ʲ_{k,m̄} − βʲ_k‖₁ ≤ C₁√(sd log(dp_j|B_{m̄}|)/(p_j|B_{m̄}|)) + C₂√(sd log(ρN)/(p_j|B_m|))
  + C₃ d √(log(dp_j|B_m|) log(ρN)/(N p_j|B_m|))`
with probability at least `1 − (6/(min_{i∈W_k} p_i|B_m|) + 4/(p_j|B_m|)
  + ∑_{i∈W_k} 7d exp(−p* p_i ψ|B_m|/(32 d x²_max)))`; stated as
`P(failure ∩ A) ≤ (that bound) · P(A)`. -/
theorem proposition_12
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N K d : ℕ} [NeZero K] (p : Fin N → ℝ) (PX : Fin N → Measure (Fin d → ℝ))
    (β : Fin N → Fin K → Fin d → ℝ) (βdag : Fin K → Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (Z : ℕ → Ω → Fin N) (Xc : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ)
    (hmodel : IsBanditModel P p PX β βdag s σ Z Xc ε)
    (Kopt : Fin N → Finset (Fin K)) (xmax b h pstar ψ L ρ : ℝ)
    (hA : BanditAssumptions PX β Kopt xmax b h pstar ψ L ρ)
    (C₀ : ℝ) (hC₀ : 2 < C₀) (hd : 2 ≤ d) (hs : 1 ≤ s) (H : ℕ) (hH : 1 ≤ H)
    (sel : LassoSelector d) (tb : ArgmaxRule K) (hsel : IsLassoSelector sel)
    (htb : IsArgmaxRule tb)
    (hadm : eta0 N d (stdTuning K d s σ p C₀ xmax h pstar ψ ρ H).b0
        (qStd K d s σ p C₀ xmax h pstar ψ) ≤ 1 / 2 - 1 / C₀ - zeta0Std d s C₀)
    (m : ℕ) (hm : 1 ≤ m)
    (hBm : (batch (stdTuning K d s σ p C₀ xmax h pstar ψ ρ H).b0 H m).Nonempty)
    (hadm1 : Real.log (d * ((batch (stdTuning K d s σ p C₀ xmax h pstar ψ ρ H).b0 H m).card : ℝ))
        ≤ (1 / 2 - 1 / C₀ - zeta0Std d s C₀) ^ 2 * ρ * N / 9)
    (j : Fin N) (k : Fin K) (hk : k ∈ Kopt j) :
    let prm := stdTuning K d s σ p C₀ xmax h pstar ψ ρ H
    let Bm : ℝ := (batch prm.b0 H m).card
    let Bbar : ℝ := (cumBatch prm.b0 H m).card
    let A := forcedGood sel tb prm β Z Xc ε h xmax
    P ({ω | constC1 σ C₀ xmax pstar ψ j
                * Real.sqrt (s * d * Real.log (d * p j * Bbar) / (p j * Bbar))
              + constC2 σ p C₀ pstar ψ j * Real.sqrt (s * d * Real.log (ρ * N) / (p j * Bm))
              + constC3 σ p C₀ pstar ψ ρ j * d
                * Real.sqrt (Real.log (d * p j * Bm) * Real.log (ρ * N) / (N * p j * Bm))
            < l1 (allEstimate sel tb prm β Z Xc ε ω m j k - β j k)} ∩ A)
      ≤ ENNReal.ofReal (6 / ((⨅ i : {i // k ∈ Kopt i}, p i) * Bm) + 4 / (p j * Bm)
          + ∑ i ∈ optInstances Kopt k,
              7 * d * Real.exp (-(pstar * p i * ψ * Bm) / (32 * d * xmax ^ 2))) * P A := by sorry

end RobustMultitask.Estimator.Supplement
