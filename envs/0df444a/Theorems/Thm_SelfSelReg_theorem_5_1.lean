-- Prove2me | Theorems.Thm_SelfSelReg_theorem_5_1
-- name    : SelfSelReg.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:46.110755+00:00
-- url     : https://prove2.me/theorems/9573af3b-5e9f-479d-9906-cf8869ac6e34
-- title:
--   Theorem 5.1 — restricted moment structure (i)–(iv)
-- statement:
--   In the Gaussian self-selection model ($n\ge1$, $2\le k\le n$) under Assumption 1.2 with constants $B\ge1$, $\Delta\in(0,1]$, let $K,T,s$ be the hyperparameters of Hyperparameters 4.1. For every non-empty $Q\subseteq[k]$:
--
--   1. **(i) Decomposition.** For every $1\le r\le s$ and $b\in\mathbb R^n$,
--   $$\mathrm{Mat}_r(\mathsf T^Q_{2r})=\sum_{i\in Q}\lambda_i^{(2r)}u_i^{\otimes r}(u_i^{\otimes r})^\top+E_r,\qquad \mathrm{Mat}_s(\mathsf T^Q_{2s+1}\lrcorner b)=\sum_{i\in Q}\lambda_i^{(2s)}\langle b,a_i\rangle u_i^{\otimes s}(u_i^{\otimes s})^\top+E(b),$$
--   with $\|E_r\|_F\le e^{8s\log K-T^2/(2K)}\sum_{i\in Q}\lambda_i^{(2r)}$ and $\|E(b)\|_F\le e^{8s\log K-T^2/(2K)}\|b\|_2\sum_{i\in Q}\lambda_i^{(2s)}$.
--   2. **(ii) Weights.** For every $i,j\in Q$ and $1\le r\le s$,
--   $$e^{-T^2}\le\mathbb P(T\le Y_i\le T+1)\le\lambda_i^{(2r)}\le e^{4r\log K-T^2/(3K)},\qquad K^{-(s-r)}\frac{\lambda_i^{(2s)}}{\lambda_j^{(2s)}}\le\frac{\lambda_i^{(2r)}}{\lambda_j^{(2r)}}\le K^{s-r}\frac{\lambda_i^{(2s)}}{\lambda_j^{(2s)}}.$$
--   3. **(iii) Near-orthogonality.** $|\langle u_i^{\otimes s},u_j^{\otimes s}\rangle|\le e^{-s/K}$ for $i\ne j$.
--   4. **(iv) Scaled regressors.** For every $i,j\in Q$, $a_i$ is a positive multiple of $w_i$,
--   $$\frac{T}{2\sqrt{2s+1}}\frac{\|w_i\|_2}{\sigma_i^2}\le\|a_i\|_2\le\frac{T+1}{\sqrt{2s+1}}\frac{\|w_i\|_2}{\sigma_i^2},\qquad \|a_i-a_j\|_2^2\ge\frac1K\max\{\|a_i\|_2^2,\|a_j\|_2^2\}\ (i\ne j).$$
--
--   Here $\mathsf T^Q_d$ is the restricted Hermite moment, $\lambda_i^{(2r)}$ the weights, $u_i=w_i/\|w_i\|_2$, $a_i$ the scaled regressors and $\sigma_i^2=1+\|w_i\|_2^2$. The restricted moments are therefore close to weighted sums of nearly orthogonal rank-one terms, the structure that the implicit tensor decomposition of Section 6 exploits.
--
--   **Formalization Note** Natural logarithm. $E_r$ and $E(b)$ are the differences of the two sides, so (i) is stated as the two Frobenius bounds on these differences.
--
--   Differences from the source:
--   - reading: s := K⁴ log n (9), printed as a real number → s = ⌈K⁴ log n⌉ (hypS), natural logarithm; reason: s is used as a tensor order ("let s ≥ 1 be an integer", Lemmas 5.7, 5.8) and (182) states s ≤ 2K⁴ log n, which presupposes rounding up; the ceiling is also the stronger choice for every bound that improves with s
--   - encoding: (20)–(21) with error terms E_r, E(b) satisfying (22) → the Frobenius bounds (22) on the differences Mat_r(T^Q_{2r}) − Σ… and Mat_s(T^Q_{2s+1} ⌟ b) − Σ…; reason: E_r and E(b) are defined by (20) and (21) as these differences
--   - encoding: K^{−(s−r)} → (K^{s−r})⁻¹ with s − r a natural number; reason: r ≤ s; same value
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Theorem 5.1, (20)–(27), p.19 (PDF p.22); proof §5.3, pp.26–28 (PDF pp.29–31)

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_SelfSelReg_jointLaw
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_Tensor
import Definitions.Def_SelfSelReg_restrictedMoment

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Theorem 5.1** (Restricted Moment Structure), parts (i)–(iv).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Theorem 5.1, p.19 (PDF p.22): "Consider the Gaussian self-selection model
(Definition 1.1) under the boundedness and uncoveredness assumptions (Assumption 1.2). Use the
hyperparameters K, T, s from Hyperparameters 4.1. The following holds for every non-empty Q ⊆ [k].
(i) For every 1 ≤ r ≤ s and b ∈ ℝⁿ, Mat_r(T^Q_{2r}) = Σ_{i∈Q} λ_i^{(2r)} u_i^{⊗r}(u_i^{⊗r})ᵀ + E_r (20),
Mat_s(T^Q_{2s+1} ⌟ b) = Σ_{i∈Q} λ_i^{(2s)} ⟨b, a_i⟩ u_i^{⊗s}(u_i^{⊗s})ᵀ + E(b) (21). The errors satisfy
‖E_r‖_F ≤ e^{8s log K − T²/(2K)} Σ_{i∈Q} λ_i^{(2r)}, ‖E(b)‖_F ≤ e^{8s log K − T²/(2K)} ‖b‖₂ Σ_{i∈Q} λ_i^{(2s)} (22).
(ii) For every i, j ∈ Q and 1 ≤ r ≤ s, the component weights satisfy
e^{−T²} ≤ P(T ≤ Y_i ≤ T + 1) ≤ λ_i^{(2r)} ≤ e^{4r log K − T²/(3K)} (23),
K^{−(s−r)} λ_i^{(2s)}/λ_j^{(2s)} ≤ λ_i^{(2r)}/λ_j^{(2r)} ≤ K^{s−r} λ_i^{(2s)}/λ_j^{(2s)} (24).
(iii) The final lifted vectors are nearly orthogonal: |⟨u_i^{⊗s}, u_j^{⊗s}⟩| ≤ e^{−s/K} (i ≠ j) (25).
(iv) For every i, j ∈ Q, a_i is a positive multiple of w_i, and
T/(2√(2s + 1)) ‖w_i‖₂/σ_i² ≤ ‖a_i‖₂ ≤ (T + 1)/√(2s + 1) ‖w_i‖₂/σ_i² (26),
‖a_i − a_j‖₂² ≥ (1/K) max{‖a_i‖₂², ‖a_j‖₂²} (i ≠ j) (27)."

**Formalization Note.**
* `K = hypK B ∆`, `s = hypS B ∆ n = ⌈K⁴ log n⌉`, `T = hypT B ∆ n = 2K²√s` (Hyperparameters 4.1;
  `s` read as the ceiling). Natural logarithm.
* `T^Q_d` is `restrictedMoment w T Q d` (16); `Mat_r` is `matFlat r`; `⌟ b` is `contractLast`;
  `λ_i^{(2r)} = weight w T i r` (18); `a_i = scaledReg w T s i` (19); `u_i = unitReg w i`;
  `σ_i² = sigmaSq w i`. `E_r` and `E(b)` are the differences of the two sides of (20) and (21), so
  (i) is the pair of Frobenius bounds (22) on those differences. -/
theorem theorem_5_1 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (B Δ : ℝ) (hB : 1 ≤ B)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (w : Fin k → EuclideanSpace ℝ (Fin n))
    (hw : SatisfiesAssumption B Δ w) (K T : ℝ) (s : ℕ) (hKdef : K = hypK B Δ)
    (hsdef : s = hypS B Δ n) (hTdef : T = hypT B Δ n) (Q : Finset (Fin k)) (hQ : Q.Nonempty) :
    -- (i)
    (∀ r : ℕ, 1 ≤ r → r ≤ s →
      matFrobNorm (matFlat r (restrictedMoment w T Q (2 * r)) -
          ∑ i ∈ Q, weight w T i r •
            Matrix.vecMulVec (tensorPow (unitReg w i) r) (tensorPow (unitReg w i) r)) ≤
        Real.exp (8 * s * Real.log K - T ^ 2 / (2 * K)) * ∑ i ∈ Q, weight w T i r) ∧
    (∀ b : EuclideanSpace ℝ (Fin n),
      matFrobNorm (matFlat s (contractLast (restrictedMoment w T Q (2 * s + 1)) b) -
          ∑ i ∈ Q, (weight w T i s * inner ℝ b (scaledReg w T s i)) •
            Matrix.vecMulVec (tensorPow (unitReg w i) s) (tensorPow (unitReg w i) s)) ≤
        Real.exp (8 * s * Real.log K - T ^ 2 / (2 * K)) * ‖b‖ * ∑ i ∈ Q, weight w T i s) ∧
    -- (ii)
    (∀ i ∈ Q, ∀ j ∈ Q, ∀ r : ℕ, 1 ≤ r → r ≤ s →
      Real.exp (-T ^ 2) ≤
          (jointLaw n k).real {z | T ≤ response w z.1 z.2 i ∧ response w z.1 z.2 i ≤ T + 1} ∧
        (jointLaw n k).real {z | T ≤ response w z.1 z.2 i ∧ response w z.1 z.2 i ≤ T + 1} ≤
          weight w T i r ∧
        weight w T i r ≤ Real.exp (4 * r * Real.log K - T ^ 2 / (3 * K)) ∧
        (K ^ (s - r))⁻¹ * (weight w T i s / weight w T j s) ≤ weight w T i r / weight w T j r ∧
        weight w T i r / weight w T j r ≤ K ^ (s - r) * (weight w T i s / weight w T j s)) ∧
    -- (iii)
    (∀ i ∈ Q, ∀ j ∈ Q, i ≠ j →
      |frobInner (tensorPow (unitReg w i) s) (tensorPow (unitReg w j) s)| ≤ Real.exp (-(s / K))) ∧
    -- (iv)
    (∀ i ∈ Q,
      (∃ c : ℝ, 0 < c ∧ scaledReg w T s i = c • w i) ∧
        T / (2 * Real.sqrt (2 * s + 1)) * (‖w i‖ / sigmaSq w i) ≤ ‖scaledReg w T s i‖ ∧
        ‖scaledReg w T s i‖ ≤ (T + 1) / Real.sqrt (2 * s + 1) * (‖w i‖ / sigmaSq w i)) ∧
    (∀ i ∈ Q, ∀ j ∈ Q, i ≠ j →
      1 / K * max (‖scaledReg w T s i‖ ^ 2) (‖scaledReg w T s j‖ ^ 2) ≤
        ‖scaledReg w T s i - scaledReg w T s j‖ ^ 2) := by sorry

end SelfSelReg
