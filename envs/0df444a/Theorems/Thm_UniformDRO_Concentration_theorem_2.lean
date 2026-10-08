-- Prove2me | Theorems.Thm_UniformDRO_Concentration_theorem_2
-- name    : UniformDRO.Concentration.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:07.507384+00:00
-- url     : https://prove2.me/theorems/94779245-d61a-429b-ba8c-7fed1932d1e1
-- title:
--   Theorem 2, p. 20 — w.p. ≥ 1 − 2e^{−t}, |R_k(θ; P̂ₙ) − R_k(θ; P₀)| ≤ 10 n^{−1/(k*∨2)} c_k² M (c_k/(c_k−1) ∨ 2)(1/k + √(t + 2 log n))
-- statement:
--   Let $P_0$ be a probability measure on $(\mathcal X,\mathcal A)$, $\Theta$ a parameter set and $\ell:\Theta\times\mathcal X\to\mathbb R$ a loss with $\ell(\theta;x)\in[0,M]$ for all $\theta\in\Theta$ and $x\in\mathcal X$, where $M\ge1$. Let $k\in(1,\infty)$, $k_*=k/(k-1)$, $\rho>0$, and $c_k(\rho)=(k(k-1)\rho+1)^{1/k}$. For $Q\ll P$ let $D_{f_k}(Q\|P)=\mathbb E_P[f_k(dQ/dP)]$ be the Cressie–Read divergence and
--   $$
--   \mathcal R_k(\theta;P)=\sup_{Q\ll P}\big\{\mathbb E_Q[\ell(\theta;X)]:D_{f_k}(Q\|P)\le\rho\big\}
--   $$
--   the robust risk. Let $X_1,\dots,X_n$ be i.i.d. $P_0$ with empirical measure $\widehat P_n$. For a fixed $\theta\in\Theta$ and $t>0$, whenever $n\ge k\vee3$, with probability at least $1-2e^{-t}$,
--   $$
--   \big|\mathcal R_k(\theta;\widehat P_n)-\mathcal R_k(\theta;P_0)\big|\le10\,n^{-\frac1{k_*\vee2}}\,c_k(\rho)^2M\Big(\frac{c_k(\rho)}{c_k(\rho)-1}\vee2\Big)\Big(\frac1k+\sqrt{t+2\log n}\Big).
--   $$
--
--   The plug-in robust risk is thus a consistent estimator of the population robust risk, at the rate $n^{-1/(k_*\vee2)}$ up to logarithmic factors; a covering argument makes the bound uniform over a model class (Corollaries 1–2).
--
--   **Formalization Note** $k\in(1,\infty)$, $M\ge1$ and the Cressie–Read family are the standing assumptions of Section 4 (p. 19). The sample is a point of $\mathcal X^n$ under the product measure $P_0^{\otimes n}$, and $\widehat P_n=\frac1n\sum_i\delta_{X_i}$. The robust risk is encoded through the likelihood-ratio form (3): the supremum of $\mathbb E_P[L\,\ell(\theta;\cdot)]$ over measurable $L\ge0$ with $\mathbb E_P[L]=1$ and $\mathbb E_P[f_k(L)]\le\rho$. The probability of the failure event is bounded as an outer measure. Measurability of $\ell(\theta;\cdot)$ is added (the loss is a random variable).
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, Theorem 2, p. 20; standing assumption §4, p. 19; proof App. C.1, pp. 38–40

import Mathlib
import Definitions.Def_UniformDRO_Concentration_RobustRisk

open MeasureTheory

namespace UniformDRO.Concentration

/-- Theorem 2 (Duchi & Namkoong, arXiv:1810.08750v6, p. 20). Assume `ℓ(θ; x) ∈ [0, M]` for all
`θ, x` (with `M ≥ 1`, the standing assumption of §4, p. 19) and `k ∈ (1, ∞)`, `ρ > 0`. For a fixed
`θ` and `t > 0`, whenever `n ≥ k ∨ 3`, with probability at least `1 - 2e^{-t}` over
`X₁, …, X_n` i.i.d. `P₀`,
`|R_k(θ; P̂_n) - R_k(θ; P₀)| ≤ 10 n^{-1/(k* ∨ 2)} c_k(ρ)² M (c_k(ρ)/(c_k(ρ) - 1) ∨ 2)(1/k + √(t + 2 log n))`.
The failure event is bounded in outer measure; measurability of `ℓ(θ; ·)` is added. -/
theorem theorem_2 {X : Type*} [MeasurableSpace X] (P₀ : Measure X) [IsProbabilityMeasure P₀]
    {Θ : Type*} (ℓ : Θ → X → ℝ) (M : ℝ) (hM : 1 ≤ M) (hℓ : ∀ θ x, ℓ θ x ∈ Set.Icc 0 M)
    (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (θ : Θ) (hmeas : Measurable (ℓ θ))
    (n : ℕ) (hnk : k ≤ n) (hn3 : 3 ≤ n) (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin n => P₀)
        {s | 10 * (n : ℝ) ^ (-(1 / max (kstar k) 2)) * ck k ρ ^ 2 * M *
              max (ck k ρ / (ck k ρ - 1)) 2 * (1 / k + Real.sqrt (t + 2 * Real.log n)) <
            |robustRisk k ρ (empiricalMeasure s) (ℓ θ) - robustRisk k ρ P₀ (ℓ θ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-t)) := by sorry

end UniformDRO.Concentration
