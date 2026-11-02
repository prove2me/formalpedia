-- Prove2me | Theorems.Thm_SpikedWishart_Separated_null_wishart_resolvent_trace_square_limit_of_trace_limit
-- name    : SpikedWishart.Separated.null_wishart_resolvent_trace_square_limit_of_trace_limit
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T02:42:53.958145+00:00
-- url     : https://prove2.me/theorems/731d5974-abc5-4d75-bbad-caaf28f3b37c
-- title:
--   Second resolvent moment of the null complex Wishart matrix outside the bulk, from the first-moment limit and the edge rate
-- statement:
--   Assume the first-moment limit `null_wishart_resolvent_trace_limit_of_moments`'s conclusion (for all admissible parameters) and the edge rate `null_wishart_top_eigenvalue_edge_rate`. With $X$, $W$, $p_n,M_n,y_n,\psi_n,x_n,A_n$ as there, for every $\varepsilon>0$
--   $$\mathbb P\Big(\Big|\tfrac1{M_n}\operatorname{Re}\operatorname{tr}A_n^2-\frac{x_n^2}{\psi_n^{-2}-y_n(1-\psi_n)^{-2}}\Big|>\varepsilon\Big)\to0 .$$
--
--   Role: second half of the resolvent trace limits, the variance of the GUE fluctuation of the secular-equation block in the parent. Proof: $\frac1M\operatorname{tr}A^2=f(x)-xf'(x)$ for the convex function $f(z)=\frac1M\operatorname{tr}A(z)$ on $z>\lambda_{\max}$; difference quotients of $f$ at $x\pm\tau$ are controlled by the first-moment limit at the shifted parameters, and the limit is the derivative of the deterministic equivalent $x\psi(x)$.
--
--   **Formalization Note**: the first-moment statement is assumed verbatim for all parameter sequences (it is applied at $\psi_n\pm\tau$).
-- source:
--   Z. D. Bai and J. W. Silverstein, CLT for linear spectral statistics of large-dimensional sample covariance matrices, Ann. Probab. 32 (2004) 553-605, https://doi.org/10.1214/aop/1078415845, Theorem 1.1 (with $f(\lambda)=(x-\lambda)^{-2}$); Z. D. Bai and J. Yao, Central limit theorems for eigenvalues in a spiked population model, Ann. Inst. H. Poincare Probab. Statist. 44 (2008) 447-474, https://doi.org/10.1214/07-AIHP118, Section 6

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE
open Filter Topology MeasureTheory Matrix
open scoped ComplexOrder

namespace SpikedWishart.Separated

theorem null_wishart_resolvent_trace_square_limit_of_trace_limit :
  (∀ (C₀ ψ₀ δ : ℝ), 0 < ψ₀ → 0 < δ → ∀ (M p : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, p n ≤ M n) →
    ∀ (y ψ : ℕ → ℝ), (∀ n, 0 ≤ y n ∧ |y n - (p n : ℝ) / M n| ≤ C₀ / M n) →
    (∀ n, ψ₀ ≤ ψ n ∧ ψ n ≤ (1 - δ) / (1 + Real.sqrt (y n))) →
    ∀ ε : ℝ, 0 < ε →
    let x : ℕ → ℝ := fun n => 1 / ψ n + y n / (1 - ψ n)
    let A : ∀ n, (Fin (M n) → Fin (p n) → ℂ) → Matrix (Fin (M n)) (Fin (M n)) ℂ := fun n X =>
      1 + (M n : ℂ)⁻¹ • (((Matrix.of X)ᵀ)ᴴ *
        ((x n : ℂ) • 1 - (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * ((Matrix.of X)ᵀ)ᴴ))⁻¹ * (Matrix.of X)ᵀ)
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (p n)).real
        {X | ε < |Real.sqrt (M n) * ((((A n X).trace).re / M n) - x n * ψ n)|}) atTop (𝓝 0)) →
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
        {X | ε < |((A n X * A n X).trace).re / M n -
          x n ^ 2 / ((ψ n)⁻¹ ^ 2 - y n / (1 - ψ n) ^ 2)|}) atTop (𝓝 0) := by sorry

end SpikedWishart.Separated
