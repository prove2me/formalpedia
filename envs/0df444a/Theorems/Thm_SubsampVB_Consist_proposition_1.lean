-- Prove2me | Theorems.Thm_SubsampVB_Consist_proposition_1
-- name    : SubsampVB.Consist.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:17.478456+00:00
-- url     : https://prove2.me/theorems/385a8c3f-1d77-4c7f-aeac-0cf33569bca6
-- title:
--   Proposition 1 — first-order input variance expansion
-- statement:
--   Let $F_i$ be independent true input laws, let $\widehat F_i$ be their empirical laws based on $n_i$ observations, and let $g_i$ be the centered influence functions of the performance measure $\psi$. Put $n=m^{-1}\sum_i n_i$, $\sigma_I^2=\operatorname{Var}[\psi(\widehat F)]$, and $\sigma_i^2=\operatorname{Var}_{F_i}[g_i(X_i)]$. Under Assumptions 1–3, as every $n_i\to\infty$ along a balanced sequence,
--
--   $$\sigma_I^2=\sum_{i=1}^{m}\frac{\sigma_i^2}{n_i}+o(n^{-1}).$$
--
--   This identifies the first-order scale of input uncertainty used in the relative-consistency results.
--
--   **Formalization Note** The data are represented by one infinite independent array, and the true-model expansion remainder and plug-in output have explicit square-integrability guards.
-- source:
--   Lam & Qian, Subsampling to enhance efficiency in input uncertainty quantification, arXiv:1811.04500v2, p. 22, Proposition 1; proof p. ec10 (PDF 60)

import Mathlib
import Definitions.Def_SubsampVB_Consist_Setting

namespace SubsampVB.Consist

open MeasureTheory Filter Finset

universe u v

/-- Proposition 1, p. 22: the first-order expansion of input variance. -/
theorem proposition_1
    {m : ℕ} [NeZero m] {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Inputs Ξ) [∀ i, IsProbabilityMeasure (F i)]
    (S : ∀ i, Set (Ξ i)) (ψ : Inputs Ξ → ℝ)
    (g : Inputs Ξ → ∀ i, Ξ i → ℝ)
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : ℕ → Fin m → ℕ)
    (hS : ∀ i, MeasurableSet (S i) ∧ F i (S i)ᶜ = 0)
    (hData : IIDData P F X) (hA1 : A1 n) (hA2 : A2 F S ψ g)
    (hA3 : A3 P F ψ g X n) :
    Tendsto (fun k => nbar (n k) *
      (sigmaI ψ P X (n k) - ∑ i : Fin m, sigma2 F g i / (n k i : ℝ)))
      atTop (nhds 0) := by sorry

end SubsampVB.Consist
