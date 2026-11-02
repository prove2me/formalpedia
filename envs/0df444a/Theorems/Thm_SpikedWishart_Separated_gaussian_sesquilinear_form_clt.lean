-- Prove2me | Theorems.Thm_SpikedWishart_Separated_gaussian_sesquilinear_form_clt
-- name    : SpikedWishart.Separated.gaussian_sesquilinear_form_clt
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T02:44:24.536458+00:00
-- url     : https://prove2.me/theorems/d90f4b1f-a8c2-40aa-918f-90c2afe141ec
-- title:
--   CLT for Gaussian sesquilinear forms: $\frac{\sqrt M}{s}\big(\frac1M HAH^*-\frac1M\operatorname{tr}A\big)\Rightarrow$ GUE
-- statement:
--   Let $H$ be an $r\times M$ matrix of i.i.d. standard complex Gaussian entries ($H=X^{\mathsf T}$ with $X\sim$ `SpikedWishart.SoftEdge.sampleLaw M r`), and let $A_n$ be deterministic Hermitian $M_n\times M_n$ matrices with $-C\le A_n\le C$ and $s_n^2=\frac1{M_n}\operatorname{tr}A_n^2\ge s_0>0$, where $M_n\to\infty$. Then
--
--   $$\frac{\sqrt{M_n}}{s_n}\Big(\frac1{M_n}HA_nH^*-\frac1{M_n}(\operatorname{tr}A_n)\,I_r\Big)\ \Longrightarrow\ \frac{Z+Z^*}{\sqrt2},$$
--
--   the $r\times r$ GUE (with $Z$ an $r\times r$ array of i.i.d. standard complex Gaussians), in the sense that $\mathbb E f(\cdot)\to\mathbb E f(\frac{Z+Z^*}{\sqrt2})$ for every bounded continuous $f$.
--
--   Role: in the parent this gives the Gaussian (GUE) fluctuation of the spiked $k\times k$ block of the secular equation, conditionally on the null block.
-- source:
--   Z. D. Bai and J. Yao, Central limit theorems for eigenvalues in a spiked population model, Ann. Inst. H. Poincare Probab. Statist. 44 (2008) 447-474, https://doi.org/10.1214/07-AIHP118, Theorem 7.1 (CLT for random sesquilinear forms), Gaussian case

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE
open Filter Topology MeasureTheory Matrix
open scoped ComplexOrder

namespace SpikedWishart.Separated

theorem gaussian_sesquilinear_form_clt :
  ∀ (r : ℕ) (C s₀ : ℝ), 0 < s₀ → ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
    ∀ (A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ), (∀ n, (A n).IsHermitian) →
    (∀ n, ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A n).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A n).PosSemidef) →
    (∀ n, s₀ ≤ ((A n * A n).trace).re / M n) →
    ∀ f : Matrix (Fin r) (Fin r) ℂ → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
    Tendsto (fun n => ∫ X, f (((Real.sqrt (M n) / Real.sqrt (((A n * A n).trace).re / M n) : ℝ) : ℂ) •
          ((M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) -
            ((M n : ℂ)⁻¹ * (A n).trace) • (1 : Matrix (Fin r) (Fin r) ℂ)))
        ∂(SpikedWishart.SoftEdge.sampleLaw (M n) r))
      atTop (𝓝 (∫ Z, f ((Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ))
        ∂(SpikedWishart.SoftEdge.sampleLaw r r))) := by sorry

end SpikedWishart.Separated
