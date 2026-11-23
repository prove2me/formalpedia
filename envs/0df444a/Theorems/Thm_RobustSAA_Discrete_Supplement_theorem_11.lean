-- Prove2me | Theorems.Thm_RobustSAA_Discrete_Supplement_theorem_11
-- name    : RobustSAA.Discrete.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:44:34.065383+00:00
-- url     : https://prove2.me/theorems/93254986-baf4-4cfc-b232-dc2b3e48de1c
-- title:
--   Theorem 11 (corrected: lower endpoint cell, Theorem 10 data, Slater point) — univariate worst case equals the conic dual (30)
-- statement:
--   Let $\Xi\subseteq\mathbb R$ be closed, $N\ge1$, data $\xi^1,\dots,\xi^N\in\Xi$ with order statistics $\xi^{(1)}\le\dots\le\xi^{(N)}$, and let $S_N\in\{D_N,V_N,W_N,U_N,A_N\}$ with threshold $Q=Q_{S_N}(\alpha)$ and region $\mathcal F^\alpha_{S_N}=\{F_0\in\mathcal P(\Xi):S_N(F_0)\le Q\}$. Assume the hypotheses of Theorem 1 ($X$ closed, $C(x_0;\mathcal F^\alpha_{S_N})<\infty$ for some $x_0\in X$, $\{c(\cdot;\xi):\xi\in\Xi\}$ equicontinuous, $X$ compact or $c$ coercive in $x$), $c(x;\cdot)$ measurable, and that some $F_0\in\mathcal P(\Xi)$ has $S_N(F_0)<Q$. Then for every $x\in X$, with $(A_{S_N},b_{S_N,\alpha},K_{S_N})$ as in Theorem 10,
--
--   $$C(x;\mathcal F^\alpha_{S_N})=\min_{r,c}\Big\{b_{S_N,\alpha}^\top r+c_{N+1}:\ -r\in K^*_{S_N},\ (A^\top_{S_N}r)_i=c_i-c_{i+1}\ (i\le N),\ c_i\ge\sup_{\xi\in\text{cell }i}c(x;\xi)\ (i\le N+1)\Big\},$$
--
--   where cell $1$ is $\Xi\cap(-\infty,\xi^{(1)}]$, cell $i$ is $\Xi\cap(\xi^{(i-1)},\xi^{(i)}]$ for $2\le i\le N$, and cell $N+1$ is $\Xi\cap(\xi^{(N)},\infty)$. The minimum is $+\infty$ when the program is infeasible and is attained otherwise.
--
--   This single-level reformulation makes Robust SAA with the five classical univariate tests a conic program.
--
--   Differences from the source:
--   - reading: Ξ with lower and upper support bounds ξ̲, ξ̄ (possibly infinite); 𝒫(Ξ) → a closed Ξ ⊆ ℝ, laws on ℝ with no mass off Ξ, data in Ξ, cells intersected with Ξ; reason: c(x;·) is only defined on the support; for Ξ = [ξ̲, ξ̄] the cells are the printed intervals
--   - correction: c₁ ≥ sup_{ξ ∈ (ξ^(0), ξ^(1)]} c(x;ξ) → c₁ ≥ c(x;ξ) on Ξ ∩ (−∞, ξ^(1)], closed at a finite lower support endpoint; reason: a law in 𝒫(Ξ) may charge ξ̲; Ξ = [0,1], N = 1, ξ¹ = ½, KS with Q = 0.9, c(x;ξ) = 𝕀[ξ = 0]: ½δ₀ + ½δ₁ is feasible with E = ½, while r = 0, c = 0 is feasible in the printed program with value 0; the proof of Theorem 13, (55), uses closed intervals; excluded: none
--   - correction: the cone data b_{W_N,α}, b_{A_N,α}, Ĩ_N of Theorem 10 as printed → the corrected data of Theorem 10; reason: see Theorem 10
--   - correction: generalized Slater point: the empirical distribution (footnote 4) → premise: some F₀ ∈ 𝒫(Ξ) satisfies the test constraints strictly; reason: F̂_N has F̂_N(ξ^(N)) = 1, so A_N(F̂_N) = ∞, and F̂_N need not be strictly feasible for small thresholds; with an empty KS region (Q < 1/(2N)) C = −∞ and the dual is unbounded, so no minimum exists; excluded: thresholds at or below inf_{F₀ ∈ 𝒫(Ξ)} S_N(F₀)
--   - reading: a cost whose expectations E_{F₀}[c(x;ξ)] are taken → c(x;·) is measurable for every x; reason: expectations of c(x;·) presuppose measurability; standing convention of the field
--   - encoding: E_{F₀}[c(x;ξ)] for any law → the integral when c(x;·) is F₀-integrable and +∞ otherwise (the published RobustSAA.Convergence.expect convention); reason: series convention; a member under which the cost is not integrable never lowers a worst case
--   - encoding: cᵢ ≥ sup over the i-th interval → cᵢ ≥ c(x;ξ) for every ξ in the i-th cell; reason: equivalent for real cᵢ; the constraint is void on an empty cell, so repeated data are allowed
--   - encoding: min_{r,c} → IsMinValue: extended-real infimum (+∞ when infeasible), attained when feasible; reason: same instances
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 11 and footnote 4, p. 18

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Univariate_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_Cones
import Definitions.Def_RobustSAA_Discrete_Supplement_UnivStat
import Definitions.Def_RobustSAA_Discrete_Supplement_UnivDual

namespace RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Univariate

theorem theorem_11 {dx N : ℕ} (hN : 0 < N) (Ξ : Set ℝ) (hΞ : IsClosed Ξ) (s : Fin N → ℝ)
    (hs : ∀ i, s i ∈ Ξ) (X : Set (RobustSAA.Convergence.Pt dx)) (hX : IsClosed X)
    (c : RobustSAA.Convergence.Pt dx → ℝ → ℝ) (hmeas : ∀ x, Measurable (c x))
    (hequi : Equicontinuous (fun ξ : ↥Ξ => fun x => c x (ξ : ℝ)))
    (hcomp : IsCompact X ∨ ∀ ξ ∈ Ξ,
      Tendsto (fun x => c x ξ) (Bornology.cobounded (RobustSAA.Convergence.Pt dx)) atTop)
    (x : RobustSAA.Convergence.Pt dx) (hx : x ∈ X) :
    (∀ Q : ℝ, (∃ x₀ ∈ X, worstCaseR (ksRegionOn Ξ Q s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ ksStat F₀ s < Q) →
      IsMinValue (worstCaseR (ksRegionOn Ξ Q s) (c x)) (univDualValues (A_KS N) (b_KS N Q) (K_KS N) Ξ (c x) s)) ∧
    (∀ Q : ℝ, (∃ x₀ ∈ X, worstCaseR (kuiperRegionOn Ξ Q s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ kuiperStat F₀ s < Q) →
      IsMinValue (worstCaseR (kuiperRegionOn Ξ Q s) (c x)) (univDualValues (A_KS N) (b_Kuiper N Q) (K_Kuiper N) Ξ (c x) s)) ∧
    (∀ Q : ℝ, (∃ x₀ ∈ X, worstCaseR (cvmRegionOn Ξ Q s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ cvmStat F₀ s < Q) →
      IsMinValue (worstCaseR (cvmRegionOn Ξ Q s) (c x)) (univDualValues (A_CvM N) (b_CvM N Q) (K_CvM N) Ξ (c x) s)) ∧
    (∀ Q : ℝ, (∃ x₀ ∈ X, worstCaseR (watsonRegionOn Ξ Q s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ watsonStat F₀ s < Q) →
      IsMinValue (worstCaseR (watsonRegionOn Ξ Q s) (c x)) (univDualValues (A_Watson N) (b_Watson N Q) (K_Watson N) Ξ (c x) s)) ∧
    (∀ Q : ℝ, (∃ x₀ ∈ X, worstCaseR (adRegionOn Ξ Q s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ adStat F₀ s < ENNReal.ofReal Q) →
      IsMinValue (worstCaseR (adRegionOn Ξ Q s) (c x)) (univDualValues (A_AD N) (b_AD N Q) (K_AD N) Ξ (c x) s)) := by sorry

end RobustSAA.Discrete.Supplement
