-- Prove2me | Theorems.Thm_SubsampVB_Consist_theorem_2
-- name    : SubsampVB.Consist.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:22.234493+00:00
-- url     : https://prove2.me/theorems/fb0603b7-d9d7-44bb-8f2e-375e2e29ade5
-- title:
--   Theorem 2 — relative consistency of Algorithm 2
-- statement:
--   Consider $m$ independent empirical input models, a performance measure $\psi$, and the proportionate subsampled variance bootstrap of Algorithm 2. Let $n=m^{-1}\sum_i n_i$, $\sigma_I^2=\operatorname{Var}[\psi(\widehat F)]$, and let $\widehat\sigma_{SVB}^2$ be the ANOVA output multiplied by the subsample ratio $\theta$. Under Assumptions 1–7, with $B,R\ge2$ and $0<\theta\le1$, if
--
--   $$B=\omega(1),\qquad BR^2=\omega((\theta n)^2),\qquad \theta=\omega(n^{-1}),$$
--
--   then
--
--   $$\frac{\widehat\sigma_{SVB}^2}{\sigma_I^2}\xrightarrow{\mathrm p}1.$$
--
--   Thus the simulation-based variance estimate has vanishing relative error as the input data sets grow.
--
--   **Formalization Note** The formal conclusion says that, for each positive error tolerance, the conditional probability given the data of a relative-error exceedance tends to zero in probability over the data. Since those probabilities lie in $[0,1]$, this is equivalent to the paper's unconditional convergence in probability. The simulation responses use an unbiased one-replication oracle and independent product laws. Integrability guards prevent default-zero expectations. The assumptions and conclusion share one sequence of sample sizes and algorithm parameters.
-- source:
--   Lam & Qian, Subsampling to enhance efficiency in input uncertainty quantification, arXiv:1811.04500v2, p. 15, Theorem 2 and (7); proof p. ec14 (PDF 64)

import Mathlib
import Definitions.Def_SubsampVB_Consist_Setting

namespace SubsampVB.Consist

open MeasureTheory Filter Finset

universe u v

/-- Theorem 2, p. 15: relative consistency of Algorithm 2. -/
theorem theorem_2
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
    ∀ ε : ℝ, 0 < ε →
      TendstoInMeasure P (fun k ω =>
        outProb (B := B k) (R := R k) simLaw (n := n k)
          (s := subsampleSize (θ k) (n k)) (dataSample X (n k) ω)
          {Y | ε < |sigmaHatSVB (θ k) Y / sigmaI ψ P X (n k) - 1|})
        atTop (fun _ => 0) := by sorry

end SubsampVB.Consist
