-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_Supplement_theorem_3
-- name    : RobustMultitask.Estimator.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:04:25.996988+00:00
-- url     : https://prove2.me/theorems/7129b1a7-3282-4ee1-8780-283f74964382
-- title:
--   Theorem 3, p. 27 (corrected: log(dT)·log(dH) for log²(dT), H = T/pⱼ, instance-specific λ, d ≥ 2) — RMBandit instance regret, standard regime
-- statement:
--   Fix $C_0>2$, the model constants $x_{\max},b,h,p_*,\psi,L,\rho$ of Assumptions 6–10, a noise bound $\sigma_{\max}$ and arrival constants $c_1>0$, $c_2$. There is a constant $C>0$ with the following property. Take any instance of the bandit model of §5 satisfying Assumptions 6–10 with these constants, with $\sigma_i\le\sigma_{\max}$ and the standard regime $c_1/N\le p_i\le c_2/N$ for all $i$, and with $d\ge2$, $N\ge2$, $s\ge1$. Let the total horizon be $H\ge1$, so that instance $j$ has expected horizon $T=p_jH$. Run RMBandit with the hyperparameters and $q$ of Appendix D.1, any LASSO selection rule and any tie-breaking rule for which the arms are measurable, and assume the explicit forms of $N=\Omega(\log d\log T)$:
--   $$\eta_0\le\frac12-\frac1{C_0}-\zeta_0,\qquad \log(dH)\le\Bigl(\frac12-\frac1{C_0}-\zeta_{1,0}\Bigr)^2\frac{\rho N}9 .$$
--   Then for every instance $j$,
--   $$R^j\le C\,Kd\Bigl(s+\frac dN\Bigr)\log(N)\,\log\bigl(d\max(T,1)\bigr)\log(dH).$$
--
--   Since $H=T/p_j=\Theta(NT)$, $\log(dH)=\log(dNT)+O(1)$; when $T\ge N$ the bound is the printed $O(Kd(s+d/N)\log(N)\log^2(dT))$. The single-instance regret thus scales as $Kd(s+d/N)$ up to logarithms, against $d^2$ for an instance learning alone.
--
--   **Formalization Note** $O(\cdot)$ and $\Theta(\cdot)$ are made uniform: $C$ is chosen after the fixed model constants and before $N,K,d,s,H$ and the instance, so it cannot depend on them. The arms must be measurable for the expected regret to be defined.
--
--   Differences from the source:
--   - correction: Rʲ_T = O(Kd(s + d/N) log(N) log²(dT)) → Rʲ ≤ C Kd(s + d/N) log(N) log(d max(T,1)) log(dH), H = T/pⱼ (one factor log(dT) becomes log(dH); max(T,1) only keeps the logarithm positive when T < 1, where the regret is at most 2b x_max); reason: the forced batch has |ℬ₀| = q log H total steps (Algorithm 2), and the target's forced regret pⱼ q log H contains the term (96x²_max Kd log(dN)/(p*ψ minᵢ pᵢ))·pⱼ log H ≥ c d log² N when H ≥ N; the proof (p. 66) writes log T for log H there; when log N/log²(dT) → ∞ (e.g. log N = k³, T = e^k, K = 2 with one arm suboptimal by h everywhere) the printed bound fails, see DISPROOF.md
--   - correction: λ₀, λ₁,₀ as maxima over instances (D.1 display) → instance-specific; reason: as in Propositions 11 and 12
--   - correction: no condition on d → d ≥ 2; reason: as in Proposition 11 (the source assumes K, d, N > 1, p. 66); excluded: d = 1
--   - reading: N = Ω(log(d) log(T)) → η₀ ≤ 1/2 − 1/C₀ − ζ₀ and log(dH) ≤ (1/2 − 1/C₀ − ζ₁,₀)² ρN/9; reason: these are the requirements stated in the proofs (pp. 60, 63), with |ℬ_m| ≤ H as on p. 63
--   - reading: total horizon T/pⱼ = Θ(NT), pⱼ = Θ(1/N) → c₁/N ≤ pᵢ ≤ c₂/N for all i, H = T/pⱼ, with C depending on c₁, c₂, σ_max and the model constants; reason: this is the uniform meaning of the source's Θ and O, whose constants depend on the fixed parameters only
--   - reading: algorithm details → as in the BanditAlgorithm definition (rounded |ℬ₀|, all-sample trimmed mean over instances with samples, min(s,d) in ζ₀, s ≥ 1, N ≥ 2); reason: see that definition and Proposition 12
--   - encoding: expected regret of RMBandit → measurable arm choices produced by arbitrary non-anticipating selection and tie-breaking rules; reason: the expectation requires a random variable; every rule is covered
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 27, Theorem 3; parameters p. 56 (Appendix D.1); proof pp. 64–66

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

/-- Theorem 3, p. 27 (proof pp. 64–66), with the hyperparameters of Appendix D.1 and a corrected
logarithmic factor (see the Formalization Note). Fix `C₀ > 2`, the model constants
`x_max, b, h, p*, ψ, L, ρ`, a noise bound `σ_max` and standard-regime arrival constants
`0 < c₁ ≤ c₂` (`c₁/N ≤ p_i ≤ c₂/N`). There is a constant `C` such that for every instance of the
bandit model satisfying Assumptions 6–10 with these constants, every `d ≥ 2`, `N ≥ 2`, `s ≥ 1`,
total horizon `H ≥ 1` (so instance `j` has expected horizon `T = p_j H`), under the explicit forms
`η₀ ≤ 1/2 − 1/C₀ − ζ₀` and `log(dH) ≤ (1/2 − 1/C₀ − ζ_{1,0})² ρN/9` of `N = Ω(log d log T)`, every
run of RMBandit with measurable arm choices has
`Rʲ ≤ C · K d (s + d/N) log N · log(d max(T, 1)) · log(dH)`, `T = p_j H`. The printed
`log²(dT)` is replaced by `log(dT) · log(dH)` (DISPROOF.md); `max(T, 1)` only keeps the
logarithm positive for an expected horizon below one. -/
theorem theorem_3 (C₀ xmax b h pstar ψ L ρ σmax c₁ c₂ : ℝ) (hC₀ : 2 < C₀) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {N K d : ℕ} [NeZero K] (p : Fin N → ℝ) (PX : Fin N → Measure (Fin d → ℝ))
        (β : Fin N → Fin K → Fin d → ℝ) (βdag : Fin K → Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
        (Z : ℕ → Ω → Fin N) (Xc : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ),
        IsBanditModel P p PX β βdag s σ Z Xc ε →
        ∀ (Kopt : Fin N → Finset (Fin K)),
        BanditAssumptions PX β Kopt xmax b h pstar ψ L ρ →
        (∀ i, (σ i : ℝ) ≤ σmax) →
        (∀ i, c₁ / N ≤ p i ∧ p i ≤ c₂ / N) →
        2 ≤ d → 2 ≤ N → 1 ≤ s →
        ∀ (H : ℕ), 1 ≤ H →
        eta0 N d (stdTuning K d s σ p C₀ xmax h pstar ψ ρ H).b0
            (qStd K d s σ p C₀ xmax h pstar ψ) ≤ 1 / 2 - 1 / C₀ - zeta0Std d s C₀ →
        Real.log (d * H) ≤ (1 / 2 - 1 / C₀ - zeta0Std d s C₀) ^ 2 * ρ * N / 9 →
        ∀ (sel : LassoSelector d) (tb : ArgmaxRule K),
        IsLassoSelector sel → IsArgmaxRule tb →
        (∀ t, Measurable (fun ω =>
          banditArm sel tb (stdTuning K d s σ p C₀ xmax h pstar ψ ρ H) β Z Xc ε ω t)) →
        ∀ (j : Fin N),
        taskRegret P β Z Xc
            (banditArm sel tb (stdTuning K d s σ p C₀ xmax h pstar ψ ρ H) β Z Xc ε) j H
          ≤ C * K * d * (s + (d : ℝ) / N) * Real.log N * Real.log (d * max (p j * H) 1)
            * Real.log (d * H) := by sorry

end RobustMultitask.Estimator.Supplement
