-- Prove2me | Theorems.Thm_SubsampVB_Consist_theorem_7
-- name    : SubsampVB.Consist.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:26.715803+00:00
-- url     : https://prove2.me/theorems/602b74d0-9f7f-4941-85c4-dfdfb1a8e019
-- title:
--   Theorem 7 — consistency without Monte Carlo error
-- statement:
--   Under Assumptions 1–4, draw $s_i=\lfloor\theta n_i\rfloor$ observations with replacement from the $i$th empirical input law, and let $\operatorname{Var}_*$ mean conditional variance over that resampling. Define $\sigma_{SVB}^2=\theta\operatorname{Var}_*[\psi(\widehat F_{s_1,1}^*,\ldots,\widehat F_{s_m,m}^*)]$ and $\sigma_I^2=\operatorname{Var}[\psi(\widehat F)]$. If $0<\theta\le1$ and $\theta n\to\infty$, where $n=m^{-1}\sum_i n_i$, then
--
--   $$\frac{\sigma_{SVB}^2}{\sigma_I^2}\xrightarrow{\mathrm p}1.$$
--
--   This isolates the accuracy of the subsampling approximation before simulation noise is added.
--
--   **Formalization Note** All limits use the same sequence of data sizes and subsample ratios. The ratio is evaluated with Lean's total division at early indices, while Assumption 3 and Proposition 1 force a positive denominator eventually.
-- source:
--   Lam & Qian, Subsampling to enhance efficiency in input uncertainty quantification, arXiv:1811.04500v2, p. 25, Theorem 7; proof p. ec13 (PDF 63)

import Mathlib
import Definitions.Def_SubsampVB_Consist_Setting

namespace SubsampVB.Consist

open MeasureTheory Filter Finset

universe u v

/-- Theorem 7, p. 25: relative consistency without Monte Carlo error. -/
theorem theorem_7
    {m : ℕ} [NeZero m] {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Inputs Ξ) [∀ i, IsProbabilityMeasure (F i)]
    (S : ∀ i, Set (Ξ i)) (ψ : Inputs Ξ → ℝ)
    (g : Inputs Ξ → ∀ i, Ξ i → ℝ)
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : ℕ → Fin m → ℕ)
    (θ : ℕ → ℝ)
    (hS : ∀ i, MeasurableSet (S i) ∧ F i (S i)ᶜ = 0)
    (hData : IIDData P F X) (hA1 : A1 n) (hA2 : A2 F S ψ g)
    (hA3 : A3 P F ψ g X n) (hA4 : A4 P F ψ g X n θ)
    (hθrange : ∀ k, 0 < θ k ∧ θ k ≤ 1)
    (hθn : Tendsto (fun k => θ k * nbar (n k)) atTop atTop) :
    TendstoInMeasure P (fun k ω =>
      sigmaSVB ψ (θ k) (dataSample X (n k) ω) / sigmaI ψ P X (n k))
      atTop (fun _ => 1) := by sorry

end SubsampVB.Consist
