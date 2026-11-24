-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_Supplement_proposition_14
-- name    : RobustMultitask.Estimator.Supplement.proposition_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:07:18.359795+00:00
-- url     : https://prove2.me/theorems/3d3e4898-b3b1-4f1f-ad8b-d34639e48873
-- title:
--   Proposition 14, p. 69 (corrected: admissibility with 4C₀, d ≥ 2) — data-poor all-sample tail bound on the event 𝒜
-- statement:
--   Work in the bandit model of §5 under Assumptions 6–10, with $C_0>2$, $d\ge2$, $s\ge1$, total horizon $H\ge1$, the data-poor instance $j$, and the data-poor RMBandit with the hyperparameters, $q$ and constants $C_4,C_5,C_6$ of Appendix D.2 (any selection and tie-breaking rules). Put $\zeta_0=\zeta_{1,0}=\frac{C_0-2}{4C_0}$. Assume $\eta_0\le\frac12-\frac1{C_0}-\zeta_0$, and let $\mathcal B_m$, $m\ge1$, be a nonempty batch with
--   $$\log(d|\mathcal B_m|)\le\Bigl(\frac12-\frac1{C_0}-\zeta_{1,0}\Bigr)^2\frac{\rho N}9=\Bigl(\frac{C_0-2}{4C_0}\Bigr)^2\frac{\rho N}9 .$$
--   Then for every optimal arm $k\in\mathcal K^j_{\mathrm{opt}}$, conditionally on the event $\mathcal A$,
--   $$\|\widehat\beta^j_{k,\bar m}-\beta^j_k\|_1\le C_4\sqrt{\frac{s^2\log(dp_j|\mathcal B_{\bar m}|)}{p_j|\mathcal B_{\bar m}|}}+C_5\sqrt{\frac{\log(\rho N)}{p_j|\mathcal B_m|}}+C_6\sqrt{\frac{\log(dp_j|\mathcal B_m|)\log(\rho N)}{Np_j|\mathcal B_m|}}$$
--   with probability at least
--   $$1-\Bigl(\frac6{\min_{i\in\mathcal W_k,i\ne j}p_i|\mathcal B_m|}+\frac4{p_j|\mathcal B_m|}+9\exp\Bigl(-\frac{p_*p_j|\mathcal B_m|}{20}\Bigr)+\sum_{i\in\mathcal W_k,i\ne j}5d\exp\Bigl(-\frac{p_*p_i\psi|\mathcal B_m|}{32dx_{\max}^2}\Bigr)\Bigr).$$
--
--   The first term scales as $s^2$ rather than $sd$: the data-poor instance learns as if its arm parameters were $s$-sparse, which gives the regret of Theorem 4.
--
--   **Formalization Note** "Conditionally on $\mathcal A$" is $\mathbb P(\text{failure}\cap\mathcal A)\le(\text{bound})\cdot\mathbb P(\mathcal A)$ with outer measures. The minimum over $\mathcal W_k\setminus\{j\}$ is over a nonempty set: the batch admissibility forces $\rho N>1$, hence $|\mathcal W_k|\ge2$.
--
--   Differences from the source:
--   - correction: log(d|ℬ_m|) ≤ ((C₀−2)/(2C₀))² ρN/9 (p. 70) → log(d|ℬ_m|) ≤ ((C₀−2)/(4C₀))² ρN/9; reason: the proof requires η ≤ 1/2 − 1/C₀ − ζ with ζ = (C₀−2)/(4C₀), i.e. η ≤ (C₀−2)/(4C₀); the printed denominator 2C₀ allows η up to twice that, outside Proposition 9's range; excluded: instances with ((C₀−2)/(4C₀))²ρN/9 < log(d|ℬ_m|) ≤ ((C₀−2)/(2C₀))²ρN/9
--   - correction: λ₀ as a maximum over instances (D.2 display) → instance-specific; reason: as in Proposition 13 (λ₁,₀ is printed instance-specific in D.2)
--   - correction: no condition on d → d ≥ 2; reason: as in Proposition 12; excluded: d = 1
--   - reading: N = Ω(log(d) log(T)) → η₀ ≤ 1/2 − 1/C₀ − ζ₀ and the batch condition above; reason: these are the requirements of the proofs (pp. 68, 70)
--   - reading: the batch Step 1 and the conditional probability → as in Proposition 12, with the donors excluding j; reason: Remark 4 and the proof (p. 69) take the trimmed mean over 𝒲_k \ {j}
--   - encoding: m unspecified, an arbitrary minimizer, s ∈ ℕ → m ≥ 1 with ℬ_m nonempty, arbitrary non-anticipating rules, s ≥ 1, H ≥ 1, |ℬ₀| = ⌈q log H⌉; reason: as in Proposition 12
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 69, Proposition 14; parameters p. 67 (Appendix D.2); proof pp. 69–70

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

/-- Proposition 14, p. 69 (proof pp. 69–70), with the hyperparameters, `q` and constants
`C₄, C₅, C₆` of Appendix D.2. Under the bandit model and Assumptions 6–10, for `C₀ > 2`, `d ≥ 2`,
`s ≥ 1`, total horizon `H ≥ 1`, the forced-stage admissibility `η₀ ≤ 1/2 − 1/C₀ − ζ₀` and, for a
batch `B_m` (`m ≥ 1`, nonempty), the all-sample admissibility
`log(d|B_m|) ≤ (1/2 − 1/C₀ − ζ_{1,0})² ρN/9` with `ζ₀ = ζ_{1,0} = (C₀−2)/(4C₀)`, the all-sample
estimator of the data-poor instance `j` and an optimal arm `k ∈ 𝒦ʲ_opt`, computed by the data-poor
RMBandit, satisfies, conditionally on the event `A` of (35),
`‖β̂ʲ_{k,m̄} − βʲ_k‖₁ ≤ C₄√(s² log(dp_j|B_{m̄}|)/(p_j|B_{m̄}|)) + C₅√(log(ρN)/(p_j|B_m|))
  + C₆√(log(dp_j|B_m|) log(ρN)/(N p_j|B_m|))`
with probability at least `1 − (6/(min_{i∈W_k, i≠j} p_i|B_m|) + 4/(p_j|B_m|)
  + 9 exp(−p* p_j|B_m|/20) + ∑_{i∈W_k, i≠j} 5d exp(−p* p_i ψ|B_m|/(32 d x²_max)))`; stated as
`P(failure ∩ A) ≤ (that bound) · P(A)`. -/
theorem proposition_14
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
    (j : Fin N)
    (hadm : eta0 N d (poorTuning K d s σ p C₀ xmax h pstar ψ ρ j H).b0
        (qPoor K d s σ p C₀ xmax h pstar ψ j) ≤ 1 / 2 - 1 / C₀ - (C₀ - 2) / (4 * C₀))
    (m : ℕ) (hm : 1 ≤ m)
    (hBm : (batch (poorTuning K d s σ p C₀ xmax h pstar ψ ρ j H).b0 H m).Nonempty)
    (hadm1 : Real.log
        (d * ((batch (poorTuning K d s σ p C₀ xmax h pstar ψ ρ j H).b0 H m).card : ℝ))
        ≤ (1 / 2 - 1 / C₀ - (C₀ - 2) / (4 * C₀)) ^ 2 * ρ * N / 9)
    (k : Fin K) (hk : k ∈ Kopt j) :
    let prm := poorTuning K d s σ p C₀ xmax h pstar ψ ρ j H
    let Bm : ℝ := (batch prm.b0 H m).card
    let Bbar : ℝ := (cumBatch prm.b0 H m).card
    let A := forcedGood sel tb prm β Z Xc ε h xmax
    P ({ω | constC4 σ C₀ xmax pstar ψ j
                * Real.sqrt ((s : ℝ) ^ 2 * Real.log (d * p j * Bbar) / (p j * Bbar))
              + constC5 d σ p C₀ pstar ψ j * Real.sqrt (Real.log (ρ * N) / (p j * Bm))
              + constC6 d σ p C₀ pstar ψ ρ j
                * Real.sqrt (Real.log (d * p j * Bm) * Real.log (ρ * N) / (N * p j * Bm))
            < l1 (allEstimate sel tb prm β Z Xc ε ω m j k - β j k)} ∩ A)
      ≤ ENNReal.ofReal (6 / ((⨅ i : {i // k ∈ Kopt i ∧ i ≠ j}, p i) * Bm) + 4 / (p j * Bm)
          + 9 * Real.exp (-(pstar * p j * Bm) / 20)
          + ∑ i ∈ (optInstances Kopt k).erase j,
              5 * d * Real.exp (-(pstar * p i * ψ * Bm) / (32 * d * xmax ^ 2))) * P A := by sorry

end RobustMultitask.Estimator.Supplement
