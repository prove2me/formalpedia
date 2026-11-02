-- Prove2me | Theorems.Thm_SpikedWishart_Separated_null_wishart_resolvent_trace_limit_of_moments
-- name    : SpikedWishart.Separated.null_wishart_resolvent_trace_limit_of_moments
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T02:42:07.378986+00:00
-- url     : https://prove2.me/theorems/8d41fc55-b9b8-4a44-b33b-e3750e92b5a6
-- title:
--   Resolvent trace of the null complex Wishart matrix outside the bulk at the $\sqrt M$ scale, from the moment bounds and the edge rate
-- statement:
--   Assume the moment bounds `null_wishart_truncated_resolvent_trace_moments` (Efron-Stein variance bound and the Marchenko-Pastur equation with explicit error) and the edge rate `null_wishart_top_eigenvalue_edge_rate`. Let $X$, $Y=X^{\mathsf T}$, $W=\frac1MYY^*$ be as there with $p_n\le M_n$, $M_n\to\infty$; let $y_n\ge0$ with $|y_n-p_n/M_n|\le C_0/M_n$ and $\psi_0\le\psi_n\le(1-\delta)/(1+\sqrt{y_n})$ ($\psi_0,\delta>0$). Put $x_n=\frac1{\psi_n}+\frac{y_n}{1-\psi_n}$ and $A_n=I_M+\frac1MY^*(x_nI_p-W)^{-1}Y$. Then for every $\varepsilon>0$
--   $$\mathbb P\Big(\Big|\sqrt{M_n}\Big(\tfrac1{M_n}\operatorname{Re}\operatorname{tr}A_n-x_n\psi_n\Big)\Big|>\varepsilon\Big)\to0 .$$
--
--   Role: first half of the resolvent trace limits used for the centring of the secular-equation block in the parent; the proof is Chebyshev for the variance bound plus root selection in the Marchenko-Pastur quadratic (the root $\psi_n - (1-p/M)/x_n$ is the one continuous from $x=\infty$).
--
--   **Formalization Note**: the two assumptions are stated verbatim as hypotheses (they are separate children); $(x_nI-W)^{-1}$ is Mathlib's matrix inverse.
-- source:
--   Z. D. Bai and J. W. Silverstein, CLT for linear spectral statistics of large-dimensional sample covariance matrices, Ann. Probab. 32 (2004) 553-605, https://doi.org/10.1214/aop/1078415845, Theorem 1.1 and Section 4 (the $O(1/M)$ mean and $O(1)$ variance of $\operatorname{tr}(x-W)^{-1}$); Z. D. Bai and J. Yao, Central limit theorems for eigenvalues in a spiked population model, Ann. Inst. H. Poincare Probab. Statist. 44 (2008) 447-474, https://doi.org/10.1214/07-AIHP118, Section 6

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE
open Filter Topology MeasureTheory Matrix
open scoped ComplexOrder

namespace SpikedWishart.Separated

theorem null_wishart_resolvent_trace_limit_of_moments :
  (∀ (M p : ℕ), 0 < M → ∀ (x e1 : ℝ), 0 ≤ e1 → e1 < x →
    let μ := SpikedWishart.SoftEdge.sampleLaw M p
    let good : Set (Fin M → Fin p → ℂ) :=
      {X | ((e1 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
        (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ)).PosSemidef}
    let F : (Fin M → Fin p → ℂ) → ℝ := good.indicator (fun X =>
      (trace (((x : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) -
        (M : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹)).re)
    let Pb : ℝ := μ.real goodᶜ
    let c : ℝ := (∫ X, F X ∂μ) / M
    let κ : ℝ := (x - e1) / (2 * x)
    let a : ℝ := (x - e1)⁻¹
    let K : ℝ := 2 / κ ^ 2 * ((M : ℝ)⁻¹) ^ 2 * (p * a ^ 4) +
      8 * ((M : ℝ)⁻¹ * (p * a ^ 2)) ^ 2 / κ ^ 4 * ((M : ℝ)⁻¹) ^ 2 * (p * a ^ 2)
    let B : ℝ := p * a + 2 * ((M : ℝ)⁻¹ * (p * a ^ 2)) / κ
    (∫ X, (F X - ∫ Y, F Y ∂μ) ^ 2 ∂μ ≤ M * (K + B ^ 2 * Pb)) ∧
    ((((M : ℝ)⁻¹) ^ 2 * (p * a ^ 2) + Pb) / 2 + (M : ℝ)⁻¹ * (a / κ) ≤ κ / 2 →
      0 ≤ c ∧ c ≤ 1 - κ / 2 ∧
      |x * c - p / M - c / (1 - c)| ≤
        4 / κ ^ 2 * ((((M : ℝ)⁻¹) ^ 2 * (p * a ^ 2) + Pb) / 2 + Pb + (M : ℝ)⁻¹ * (a / κ)) +
        4 / κ ^ 3 * (4 * (((M : ℝ)⁻¹) ^ 2 * (p * a ^ 2) + (K + B ^ 2 * Pb) / M + Pb +
          ((M : ℝ)⁻¹ * (a / κ)) ^ 2)) +
        ((p : ℝ) / M + 2 / κ) * Pb)) →
  (∀ (ε : ℝ), 0 < ε → ∀ (l : ℕ) (M N : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, N n ≤ M n) →
    Tendsto (fun n => (M n : ℝ) ^ l * (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
        {X | (1 + Real.sqrt ((N n : ℝ) / M n)) ^ 2 + ε < largestEig (M n) 1 (fun _ => 1) X})
      atTop (𝓝 0)) →
  ∀ (C₀ ψ₀ δ : ℝ), 0 < ψ₀ → 0 < δ → ∀ (M p : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, p n ≤ M n) →
    ∀ (y ψ : ℕ → ℝ), (∀ n, 0 ≤ y n ∧ |y n - (p n : ℝ) / M n| ≤ C₀ / M n) →
    (∀ n, ψ₀ ≤ ψ n ∧ ψ n ≤ (1 - δ) / (1 + Real.sqrt (y n))) →
    ∀ ε : ℝ, 0 < ε →
    let x : ℕ → ℝ := fun n => 1 / ψ n + y n / (1 - ψ n)
    let A : ∀ n, (Fin (M n) → Fin (p n) → ℂ) → Matrix (Fin (M n)) (Fin (M n)) ℂ := fun n X =>
      1 + (M n : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x n : ℂ) • 1 - (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | ε < |Real.sqrt (M n) * ((((A n X).trace).re / M n) - x n * ψ n)|}) atTop (𝓝 0) := by sorry

end SpikedWishart.Separated
