-- Prove2me | Theorems.Thm_SubsampVB_Consist_theorem_2_mse_rate
-- name    : SubsampVB.Consist.theorem_2_mse_rate
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T20:54:41.85405+00:00
-- url     : https://prove2.me/theorems/a42402c0-36d5-41a4-b464-cf2c43e2bf91
-- title:
--   Proof of Theorem 2 — the Monte Carlo MSE of Algorithm 2 is $o_p(n^{-2})$
-- statement:
--   Consider $m$ independent empirical input models, a performance measure $\psi$, and the proportionate subsampled variance bootstrap of Algorithm 2 with $B$ outer resamples, $R$ inner simulation replications and subsample ratio $\theta$, so that $s_i=\lfloor\theta n_i\rfloor$. Let $n=m^{-1}\sum_i n_i$ and let $\widehat\sigma_{SVB}^2$ be Algorithm 2's output (the ANOVA estimate multiplied by $\theta$), and $\sigma_{SVB}^2$ the exact subsampled bootstrap variance (8). Under Assumptions 1–7, with $B,R\ge 2$, $0<\theta\le 1$ and the budget configuration (7)
--
--   $$B=\omega(1),\qquad BR^2=\omega((\theta n)^2),\qquad \theta n\to\infty,$$
--
--   the conditional mean squared Monte Carlo error of Algorithm 2 (over the with-replacement index maps and the simulation replications, given the data) is $o_p(n^{-2})$:
--
--   $$n^2\,\mathbb E_*\big[(\widehat\sigma_{SVB}^2-\sigma_{SVB}^2)^2\big]\xrightarrow{\mathrm p}0 .$$
--
--   This is the first step of the proof of Theorem 2 on p. ec14 ("we have $\operatorname{Var}_*[\widehat\sigma^2_{SVB}]=o_p(1/n^2)$"); by the unbiasedness part of Lemma 1, $\operatorname{Var}_*[\widehat\sigma^2_{SVB}]$ equals this conditional mean squared error. In the paper it follows from the variance formula in the proof of Lemma 1: the leading term is $\frac2B\big(\sum_i\sigma_i^2/n_i+\tau^2\theta/R\big)^2$ plus lower-order terms, and $n^2$ times it vanishes under (7).
--
--   **Formalization Note** The hypotheses are exactly those of Theorem 2 (no positivity of $\tau^2$ is assumed; the $o_p(n^{-2})$ bound is an upper bound and remains valid when $\tau^2=0$). The conditional expectation is the platform's `outMSE`: the uniform average over the $B$ independent index maps of the Bochner integral against the product law of the $B\times R$ simulation outputs. Data sizes and algorithm parameters are one common sequence indexed by $k$.
-- source:
--   Lam & Qian, Subsampling to enhance efficiency in input uncertainty quantification, arXiv:1811.04500v2, proof of Theorem 2, p. ec14 (PDF 64), first sentence; configuration (7) p. 15; variance formula in the proof of Lemma 1, p. ec14

import Mathlib
import Definitions.Def_SubsampVB_Consist_Setting

namespace SubsampVB.Consist

open MeasureTheory Filter Finset

universe u v

/-- Proof of Theorem 2, p. ec14: under (7), the conditional MSE of Algorithm 2 is `o_p(n⁻²)`. -/
theorem theorem_2_mse_rate
    {m : ℕ} [NeZero m] {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Inputs Ξ) [∀ i, IsProbabilityMeasure (F i)]
    (S : ∀ i, Set (Ξ i)) (ψ : Inputs Ξ → ℝ)
    (g : Inputs Ξ → ∀ i, Ξ i → ℝ) (simLaw : Inputs Ξ → Measure ℝ)
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : ℕ → Fin m → ℕ)
    (θ : ℕ → ℝ) (B R : ℕ → ℕ)
    (hS : ∀ i, MeasurableSet (S i) ∧ F i (S i)ᶜ = 0)
    (hData : IIDData P F X) (hOracle : SimOracle ψ simLaw)
    (hTauFinite : Integrable (fun y => (y - ψ F) ^ 2) (simLaw F))
    (hA1 : A1 n) (hA2 : A2 F S ψ g) (hA3 : A3 P F ψ g X n)
    (hA4 : A4 P F ψ g X n θ) (hA5 : A5 P F ψ simLaw X n)
    (hA6 : A6 P ψ simLaw X n θ) (hA7 : A7 P ψ simLaw X n θ)
    (hParams : ∀ k, 2 ≤ B k ∧ 2 ≤ R k ∧ 0 < θ k ∧ θ k ≤ 1)
    (hB : Tendsto (fun k => (B k : ℝ)) atTop atTop)
    (hBR2 : Tendsto (fun k =>
      (B k : ℝ) * (R k : ℝ) ^ 2 / (θ k * nbar (n k)) ^ 2) atTop atTop)
    (hθn : Tendsto (fun k => θ k * nbar (n k)) atTop atTop) :
    TendstoInMeasure P (fun k ω =>
      nbar (n k) ^ 2 *
        outMSE (B := B k) (R := R k) ψ simLaw (n := n k)
          (s := subsampleSize (θ k) (n k)) (θ k) (dataSample X (n k) ω))
      atTop (fun _ => 0) := by sorry

end SubsampVB.Consist
