-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_Supplement_theorem_4
-- name    : RobustMultitask.Estimator.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:08:08.37575+00:00
-- url     : https://prove2.me/theorems/02ce2483-d6af-4b9a-ba89-300bc1e7a20a
-- title:
--   Theorem 4, p. 28 (corrected: log(dT)·log(dH) for log²(dT), H = T/pⱼ, admissibility with 4C₀, d ≥ 2) — RMBandit data-poor instance regret
-- statement:
--   Fix $C_0>2$, the model constants $x_{\max},b,h,p_*,\psi,L,\rho$ of Assumptions 6–10, a noise bound $\sigma_{\max}$ and arrival constants $c_1>0$, $c_2$. There is a constant $C>0$ with the following property. Take any instance of the bandit model of §5 satisfying Assumptions 6–10 with these constants and $\sigma_i\le\sigma_{\max}$, a data-poor instance $j$ with
--   $$\frac{c_1}N\le p_i\le\frac{c_2}N\ (i\ne j),\qquad \frac{c_1}{d^2N}\le p_j\le\frac{c_2}{d^2N},$$
--   and $d\ge2$, $N\ge2$, $s\ge1$. Let the total horizon be $H\ge1$, so $j$ has expected horizon $T=p_jH$. Run the data-poor RMBandit with the hyperparameters and $q$ of Appendix D.2, any LASSO selection and tie-breaking rules for which the arms are measurable, and assume, with $\zeta_0=\zeta_{1,0}=\frac{C_0-2}{4C_0}$,
--   $$\eta_0\le\frac12-\frac1{C_0}-\zeta_0,\qquad\log(dH)\le\Bigl(\frac12-\frac1{C_0}-\zeta_{1,0}\Bigr)^2\frac{\rho N}9 .$$
--   Then
--   $$R^j\le C\,Ks^2\log(N)\,\log\bigl(d\max(T,1)\bigr)\log(dH).$$
--
--   Here $H=\Theta(d^2NT)$, so $\log(dH)=O(\log(dNT))$: the regret of the data-poor instance depends on the dimension only through logarithms, as if its dense arm parameters were $s$-sparse.
--
--   **Formalization Note** $C$ is chosen after the fixed model constants and before $N,K,d,s,H$ and the instance. The arms must be measurable for the expected regret to be defined.
--
--   Differences from the source:
--   - correction: Rʲ_T = O(Ks² log(N) log²(dT)) → Rʲ ≤ C Ks² log(N) log(d max(T,1)) log(dH), H = T/pⱼ (one factor log(dT) becomes log(dH); max(T,1) only keeps the logarithm positive when T < 1); reason: the target's forced regret pⱼ q log H contains pⱼ·576C₀²x²_max(max_{i≠j} d²σᵢ²/pᵢ)Ks² log N/(h²p*ψ)·log H ≥ c Ks² log² N since H ≥ N; the proof (p. 71) writes log T for log H; the printed bound fails when log N/log²(dT) → ∞, see DISPROOF.md
--   - correction: the remainder max_{i∈[N]} 896x²_max d²pⱼ/(p*ψpᵢN) (p. 70) → donor indexing i ≠ j; reason: the remainder comes from integrating dN exp(−p*ψ(min_{i≠j} pᵢ)t/(128dx²_max)) (Lemma 17), whose minimum is over donors; with i = j it would add d²/N, not O(Ks²); this changes no hypothesis or conclusion of the Lean statement, only the proof route
--   - correction: log(d|ℬ_m|) ≤ ((C₀−2)/(2C₀))² ρN/9 (p. 70) → the requirement η ≤ 1/2 − 1/C₀ − ζ₁,₀ with ζ₁,₀ = (C₀−2)/(4C₀), i.e. ((C₀−2)/(4C₀))²; reason: as in Proposition 14
--   - correction: λ₀ as a maximum over instances → instance-specific; d ≥ 2; reason: as in Propositions 13 and 14; excluded d = 1
--   - reading: total horizon T/pⱼ = Θ(d²NT), pⱼ = Θ(pⱼ′/d²) → the two-sided arrival bounds above, H = T/pⱼ, C depending on c₁, c₂, σ_max and the model constants; reason: the uniform meaning of Θ and O
--   - reading: N = Ω(log(d) log(T)) and algorithm details → the two admissibility conditions and the data-poor RMBandit definition (donors exclude j, rounded |ℬ₀|, s ≥ 1, N ≥ 2); reason: as in Theorem 3 and Proposition 14
--   - encoding: expected regret → measurable arms from arbitrary non-anticipating rules; reason: as in Theorem 3
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 28, Theorem 4; parameters p. 67 (Appendix D.2); proof pp. 67–71

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

/-- Theorem 4, p. 28 (proof pp. 67–71), with the hyperparameters of Appendix D.2 and a corrected
logarithmic factor (see the Formalization Note). Fix `C₀ > 2`, the model constants
`x_max, b, h, p*, ψ, L, ρ`, a noise bound `σ_max` and data-poor arrival constants `0 < c₁ ≤ c₂`
(`c₁/N ≤ p_i ≤ c₂/N` for `i ≠ j`, `c₁/(d²N) ≤ p_j ≤ c₂/(d²N)`). There is a constant `C` such that
for every instance of the bandit model satisfying Assumptions 6–10 with these constants, every
`d ≥ 2`, `N ≥ 2`, `s ≥ 1`, total horizon `H ≥ 1` (so the data-poor instance `j` has expected
horizon `T = p_j H`), under the explicit forms `η₀ ≤ 1/2 − 1/C₀ − ζ₀` and
`log(dH) ≤ (1/2 − 1/C₀ − ζ_{1,0})² ρN/9` (`ζ₀ = ζ_{1,0} = (C₀−2)/(4C₀)`) of
`N = Ω(log d log T)`, every run of the data-poor RMBandit with measurable arm choices has
`Rʲ ≤ C · K s² log N · log(d max(T, 1)) · log(dH)`, `T = p_j H`. The printed `log²(dT)` is
replaced by `log(dT) · log(dH)` (DISPROOF.md); `max(T, 1)` only keeps the logarithm positive for
an expected horizon below one. -/
theorem theorem_4 (C₀ xmax b h pstar ψ L ρ σmax c₁ c₂ : ℝ) (hC₀ : 2 < C₀) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {N K d : ℕ} [NeZero K] (p : Fin N → ℝ) (PX : Fin N → Measure (Fin d → ℝ))
        (β : Fin N → Fin K → Fin d → ℝ) (βdag : Fin K → Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
        (Z : ℕ → Ω → Fin N) (Xc : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ),
        IsBanditModel P p PX β βdag s σ Z Xc ε →
        ∀ (Kopt : Fin N → Finset (Fin K)),
        BanditAssumptions PX β Kopt xmax b h pstar ψ L ρ →
        (∀ i, (σ i : ℝ) ≤ σmax) →
        ∀ (j : Fin N),
        (∀ i, i ≠ j → c₁ / N ≤ p i ∧ p i ≤ c₂ / N) →
        c₁ / ((d : ℝ) ^ 2 * N) ≤ p j → p j ≤ c₂ / ((d : ℝ) ^ 2 * N) →
        2 ≤ d → 2 ≤ N → 1 ≤ s →
        ∀ (H : ℕ), 1 ≤ H →
        eta0 N d (poorTuning K d s σ p C₀ xmax h pstar ψ ρ j H).b0
            (qPoor K d s σ p C₀ xmax h pstar ψ j) ≤ 1 / 2 - 1 / C₀ - (C₀ - 2) / (4 * C₀) →
        Real.log (d * H) ≤ (1 / 2 - 1 / C₀ - (C₀ - 2) / (4 * C₀)) ^ 2 * ρ * N / 9 →
        ∀ (sel : LassoSelector d) (tb : ArgmaxRule K),
        IsLassoSelector sel → IsArgmaxRule tb →
        (∀ t, Measurable (fun ω =>
          banditArm sel tb (poorTuning K d s σ p C₀ xmax h pstar ψ ρ j H) β Z Xc ε ω t)) →
        taskRegret P β Z Xc
            (banditArm sel tb (poorTuning K d s σ p C₀ xmax h pstar ψ ρ j H) β Z Xc ε) j H
          ≤ C * K * (s : ℝ) ^ 2 * Real.log N * Real.log (d * max (p j * H) 1)
            * Real.log (d * H) := by sorry

end RobustMultitask.Estimator.Supplement
