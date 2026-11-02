-- Prove2me | Theorems.Thm_SpikedWishart_Separated_null_wishart_truncated_resolvent_trace_moments
-- name    : SpikedWishart.Separated.null_wishart_truncated_resolvent_trace_moments
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T02:41:13.948175+00:00
-- url     : https://prove2.me/theorems/0e27623b-7faf-4582-b436-a78414cad81c
-- title:
--   Truncated resolvent trace of the null complex Wishart matrix: Efron-Stein variance bound and the Marchenko-Pastur equation with $O(1/M)$ error
-- statement:
--   Let $X$ be an $M\times p$ array of i.i.d. standard complex Gaussian entries (law `SpikedWishart.SoftEdge.sampleLaw M p`), $Y=X^{\mathsf T}$ and $W=\frac1M YY^*$ ($p\times p$). Fix $0\le e_1<x$, let $\mathcal G=\{W\preceq e_1\}$, $F=\mathbf 1_{\mathcal G}\operatorname{Re}\operatorname{tr}(x-W)^{-1}$, $P_b=\mathbb P(\mathcal G^c)$, $c=\mathbb E F/M$, $\kappa=\frac{x-e_1}{2x}$, $a=(x-e_1)^{-1}$,
--   $$K=\frac{2}{\kappa^2}\frac{p a^4}{M^2}+\frac{8}{\kappa^4}\Big(\frac{pa^2}{M}\Big)^2\frac{pa^2}{M^2},\qquad B=pa+\frac{2pa^2}{M\kappa}.$$
--   Then (i) $\operatorname{Var}F\le M\,(K+B^2P_b)$; (ii) if $\frac12\big(\frac{pa^2}{M^2}+P_b\big)+\frac{a}{M\kappa}\le\frac\kappa2$, then $0\le c\le 1-\frac\kappa2$ and
--   $$\Big|x c-\frac pM-\frac{c}{1-c}\Big|\le \frac4{\kappa^2}\Big(\frac{\frac{pa^2}{M^2}+P_b}{2}+P_b+\frac{a}{M\kappa}\Big)+\frac4{\kappa^3}\cdot4\Big(\frac{pa^2}{M^2}+\frac{K+B^2P_b}{M}+P_b+\Big(\frac{a}{M\kappa}\Big)^2\Big)+\Big(\frac pM+\frac2\kappa\Big)P_b .$$
--
--   Role: (i) is the Efron-Stein bound for the resolvent trace (one column resampled at a time, rank-one resolvent identity) and (ii) says that the normalised mean solves the Marchenko-Pastur self-consistent equation $xc-y=c/(1-c)$ up to $O(1/M)+O(P_b)$; together with the edge rate they give part (i) of the resolvent trace limits.
--
--   **Formalization Note**: the explicit constants are those produced by the standard argument (leave-one-out resolvent, second-order Taylor expansion of $c\mapsto c/(1-c)$); the truncation to $\mathcal G$ keeps every quantity bounded.
-- source:
--   Efron-Stein inequality: S. Boucheron, G. Lugosi and P. Massart, Concentration Inequalities, Oxford 2013, https://doi.org/10.1093/acprof:oso/9780199535255.001.0001, Theorem 3.1; Marchenko-Pastur equation via the leave-one-out resolvent: Z. D. Bai and J. W. Silverstein, Spectral Analysis of Large Dimensional Random Matrices, 2nd ed., Springer 2010, https://doi.org/10.1007/978-1-4419-0661-8, Chapter 3, Section 3.3 (Stieltjes-transform proof of the Marchenko-Pastur law, leave-one-out identity)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE
open Filter Topology MeasureTheory Matrix
open scoped ComplexOrder

namespace SpikedWishart.Separated

theorem null_wishart_truncated_resolvent_trace_moments :
  ∀ (M p : ℕ), 0 < M → ∀ (x e1 : ℝ), 0 ≤ e1 → e1 < x →
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
        ((p : ℝ) / M + 2 / κ) * Pb) := by sorry

end SpikedWishart.Separated
