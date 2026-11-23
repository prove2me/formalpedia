-- Prove2me | Theorems.Thm_RobustSAA_Discrete_Supplement_theorem_12
-- name    : RobustSAA.Discrete.Supplement.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:45:42.540329+00:00
-- url     : https://prove2.me/theorems/858c1917-578a-40aa-9783-d4d620dd25c6
-- title:
--   Theorem 12 (corrected: lower endpoint cell, Theorem 10 data, Slater point) — univariate worst case with a moment test equals the dual (31)
-- statement:
--   In the setting of Theorem 11, let $\varphi:\Xi\to\mathbb R_+$ be measurable with $|c(x_0;\xi)|\le\nu+\eta\varphi(\xi)$ on $\Xi$ for some $x_0\in X$ and constants $\nu,\eta$ (the reading of $|c(x_0;\xi)|=O(\varphi(\xi))$), $\hat\mu=\frac1N\sum_i\varphi(\xi^i)$, and let
--   $$\mathcal F^{\alpha_1,\alpha_2}_{S_N,M_N}=\{F_0\in\mathcal P(\Xi): S_N(F_0)\le Q,\ \mathbb E_{F_0}[\varphi]<\infty,\ |\mathbb E_{F_0}[\varphi]-\hat\mu|\le Q_M\}$$
--   with $Q=Q_{S_N}(\alpha_1)$ and $Q_M=Q^{\alpha_2}_{M_N}$. Assume the hypotheses of Theorem 1 for this region, $c(x;\cdot)$ measurable, and that some $F_0\in\mathcal P(\Xi)$ has $S_N(F_0)<Q$, $\mathbb E_{F_0}[\varphi]<\infty$ and $|\mathbb E_{F_0}[\varphi]-\hat\mu|<Q_M$. Then for every $x\in X$,
--
--   $$C(x;\mathcal F^{\alpha_1,\alpha_2}_{S_N,M_N})=\min\Big\{b^\top_{S_N,\alpha_1}r+c_{N+1}+(\hat\mu+Q_M)t-(\hat\mu-Q_M)s\Big\}$$
--
--   over $-r\in K^*_{S_N}$, $t\ge0$, $s\ge0$, $c\in\mathbb R^{N+1}$ with $(A^\top_{S_N}r)_i=c_i-c_{i+1}$ for $i\le N$ and $c_i\ge\sup_{\xi\in\text{cell }i}\big(c(x;\xi)-(t-s)\varphi(\xi)\big)$ for $i\le N+1$, the cells being those of Theorem 11. The minimum is $+\infty$ when infeasible and attained otherwise.
--
--   With unbounded support the moment test is what keeps the worst case finite (Proposition 2), and this is the reformulation used in that case.
--
--   Differences from the source:
--   - reading: Ξ with lower and upper support bounds ξ̲, ξ̄ (possibly infinite); 𝒫(Ξ) → a closed Ξ ⊆ ℝ, laws on ℝ with no mass off Ξ, data in Ξ, cells intersected with Ξ; reason: c(x;·) is only defined on the support; for Ξ = [ξ̲, ξ̄] the cells are the printed intervals
--   - correction: c₁ ≥ sup_{ξ ∈ (ξ^(0), ξ^(1)]} c(x;ξ) → c₁ ≥ c(x;ξ) on Ξ ∩ (−∞, ξ^(1)], closed at a finite lower support endpoint; reason: a law in 𝒫(Ξ) may charge ξ̲; Ξ = [0,1], N = 1, ξ¹ = ½, KS with Q = 0.9, c(x;ξ) = 𝕀[ξ = 0]: ½δ₀ + ½δ₁ is feasible with E = ½, while r = 0, c = 0 is feasible in the printed program with value 0; the proof of Theorem 13, (55), uses closed intervals; excluded: none
--   - correction: the cone data b_{W_N,α}, b_{A_N,α}, Ĩ_N of Theorem 10 as printed → the corrected data of Theorem 10; reason: see Theorem 10
--   - correction: generalized Slater point: the empirical distribution (footnote 4) → premise: some F₀ ∈ 𝒫(Ξ) satisfies the test constraint and the moment constraint strictly; reason: as in Theorem 11 (A_N(F̂_N) = ∞); F̂_N meets the moment constraint strictly exactly when Q_M > 0; excluded: thresholds without a strictly feasible law
--   - reading: φ : Ξ → ℝ₊ with E_F φ < ∞ and |c(x₀;ξ)| = O(φ(ξ)) → measurable φ ≥ 0 on Ξ with |c(x₀;ξ)| ≤ ν + ηφ(ξ) on Ξ for some x₀ ∈ X; the data-generating F does not appear; reason: p. 10 reading as in the published Assumption 3; the identity is deterministic in the data
--   - encoding: |E_{F₀}φ − μ̂| ≤ Q_M → E_{F₀}φ < ∞ (lower integral) and |∫φ dF₀ − μ̂| ≤ Q_M; reason: an infinite moment violates the two-sided bound
--   - reading: a cost whose expectations E_{F₀}[c(x;ξ)] are taken → c(x;·) is measurable for every x; reason: expectations of c(x;·) presuppose measurability; standing convention of the field
--   - encoding: E_{F₀}[c(x;ξ)] for any law → the integral when c(x;·) is F₀-integrable and +∞ otherwise (the published RobustSAA.Convergence.expect convention); reason: series convention; a member under which the cost is not integrable never lowers a worst case
--   - encoding: cᵢ ≥ sup over the i-th interval → cᵢ ≥ c(x;ξ) for every ξ in the i-th cell; reason: equivalent for real cᵢ; the constraint is void on an empty cell, so repeated data are allowed
--   - encoding: min_{r,c} → IsMinValue: extended-real infimum (+∞ when infeasible), attained when feasible; reason: same instances
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 12 and footnote 4, p. 18; moment test (9)–(11), p. 10

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Univariate_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_Cones
import Definitions.Def_RobustSAA_Discrete_Supplement_UnivStat
import Definitions.Def_RobustSAA_Discrete_Supplement_UnivDual

namespace RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Univariate

theorem theorem_12 {dx N : ℕ} (hN : 0 < N) (Ξ : Set ℝ) (hΞ : IsClosed Ξ) (s : Fin N → ℝ)
    (hs : ∀ i, s i ∈ Ξ) (X : Set (RobustSAA.Convergence.Pt dx)) (hX : IsClosed X)
    (c : RobustSAA.Convergence.Pt dx → ℝ → ℝ) (hmeas : ∀ x, Measurable (c x))
    (hequi : Equicontinuous (fun ξ : ↥Ξ => fun x => c x (ξ : ℝ)))
    (hcomp : IsCompact X ∨ ∀ ξ ∈ Ξ,
      Tendsto (fun x => c x ξ) (Bornology.cobounded (RobustSAA.Convergence.Pt dx)) atTop)
    (φ : ℝ → ℝ) (hφm : Measurable φ) (hφ : ∀ ξ ∈ Ξ, 0 ≤ φ ξ)
    (hφc : ∃ x₀ ∈ X, ∃ ν η : ℝ, ∀ ξ ∈ Ξ, |c x₀ ξ| ≤ ν + η * φ ξ)
    (x : RobustSAA.Convergence.Pt dx) (hx : x ∈ X) :
    (∀ Q QM : ℝ, (∃ x₀ ∈ X, worstCaseR (ksRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ ksStat F₀ s < Q ∧
        ∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(F₀ : Measure ℝ) < ⊤ ∧
        |(∫ ξ, φ ξ ∂(F₀ : Measure ℝ)) - phiHat φ s| < QM) →
      IsMinValue (worstCaseR (ksRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x))
        (momentDualValues (A_KS N) (b_KS N Q) (K_KS N) Ξ (c x) φ QM s)) ∧
    (∀ Q QM : ℝ, (∃ x₀ ∈ X, worstCaseR (kuiperRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ kuiperStat F₀ s < Q ∧
        ∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(F₀ : Measure ℝ) < ⊤ ∧
        |(∫ ξ, φ ξ ∂(F₀ : Measure ℝ)) - phiHat φ s| < QM) →
      IsMinValue (worstCaseR (kuiperRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x))
        (momentDualValues (A_KS N) (b_Kuiper N Q) (K_Kuiper N) Ξ (c x) φ QM s)) ∧
    (∀ Q QM : ℝ, (∃ x₀ ∈ X, worstCaseR (cvmRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ cvmStat F₀ s < Q ∧
        ∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(F₀ : Measure ℝ) < ⊤ ∧
        |(∫ ξ, φ ξ ∂(F₀ : Measure ℝ)) - phiHat φ s| < QM) →
      IsMinValue (worstCaseR (cvmRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x))
        (momentDualValues (A_CvM N) (b_CvM N Q) (K_CvM N) Ξ (c x) φ QM s)) ∧
    (∀ Q QM : ℝ, (∃ x₀ ∈ X, worstCaseR (watsonRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ watsonStat F₀ s < Q ∧
        ∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(F₀ : Measure ℝ) < ⊤ ∧
        |(∫ ξ, φ ξ ∂(F₀ : Measure ℝ)) - phiHat φ s| < QM) →
      IsMinValue (worstCaseR (watsonRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x))
        (momentDualValues (A_Watson N) (b_Watson N Q) (K_Watson N) Ξ (c x) φ QM s)) ∧
    (∀ Q QM : ℝ, (∃ x₀ ∈ X, worstCaseR (adRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ adStat F₀ s < ENNReal.ofReal Q ∧
        ∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(F₀ : Measure ℝ) < ⊤ ∧
        |(∫ ξ, φ ξ ∂(F₀ : Measure ℝ)) - phiHat φ s| < QM) →
      IsMinValue (worstCaseR (adRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x))
        (momentDualValues (A_AD N) (b_AD N Q) (K_AD N) Ξ (c x) φ QM s)) := by sorry

end RobustSAA.Discrete.Supplement
