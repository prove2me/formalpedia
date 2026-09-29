-- Prove2me | Theorems.Thm_ValuativeSYZ_thm_1_8_weak_comparison_of_valuative_independence
-- name    : ValuativeSYZ.thm_1_8_weak_comparison_of_valuative_independence
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-15T11:17:20.258251+00:00
-- url     : https://prove2.me/theorems/da1be9b1-0d0c-451f-9a66-021aec723440
-- title:
--   Theorem 1.8: valuative independence implies the weak comparison property
-- statement:
--   **Theorem 1.8 of the source paper.** Let $\pi \colon (X,L) \to D^{*}$ be a polarised maximal
--   degeneration of compact Calabi–Yau manifolds, with a semistable SNC model. Assume that for every
--   $l \ge 0$ the $K$-vector space $H^0(X_K, lL)$ admits a basis satisfying valuative independence:
--   for every point $x$ of the essential skeleton, viewed as a valuation, and all coefficients
--   $a_\alpha \in K$,
--   $$v_x\Big(\sum_\alpha a_\alpha \theta^l_\alpha\Big) \;=\;
--   \min_{\alpha \,:\, a_\alpha \neq 0}\big(v(a_\alpha) + v_x(\theta^l_\alpha)\big).$$
--   Then the weak comparison property holds for the degeneration: the non-archimedean Calabi–Yau
--   potential $\varphi_0$, the solution of $\mathrm{MA}(\varphi_0) = (L^n)\mu_0$, factors through the
--   retraction map $r_{\mathcal{X}} \colon X_K^{\mathrm{an}} \to \Delta_{\mathcal{X}}$ over an open
--   subset of the skeleton of full Lebesgue measure.
--
--   Together with the reduction of the metric SYZ conjecture to the weak comparison property, and with
--   the announced existence of valuatively independent bases, this is the step that would give the
--   metric SYZ conjecture for all polarised maximal degenerations.
--
--   The statement is formalized relative to the `Degeneration` interface, which supplies the Berkovich
--   space, the dual complex, the skeleton, the section spaces with their valuations, and — as
--   hypotheses — the results of non-archimedean pluripotential theory quoted in §2 of the paper. The
--   index set of the basis is taken to be $\{0,\dots,m-1\}$ for some $m$, reflecting finite
--   dimensionality of the section spaces.
-- source:
--   Yang Li, *Valuative independence and metric SYZ conjecture*, arXiv:2605.00516v1 (1 May 2026), https://arxiv.org/abs/2605.00516, pp. 4, Theorem 1.8

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

set_option autoImplicit false

open MeasureTheory

namespace ValuativeSYZ

/-- **Theorem 1.8.** For a polarised maximal degeneration of compact Calabi–Yau manifolds
with a semistable SNC model, if for every `l ≥ 0` the space of sections `H⁰(X_K, lL)` admits a
`K`-basis satisfying valuative independence, then the weak comparison property holds for the
non-archimedean Calabi–Yau potential. -/
theorem thm_1_8_weak_comparison_of_valuative_independence
    {Berk : Type} [MeasurableSpace Berk] {K : Type} [Field K]
    {Sect : ℕ → Type} [∀ l, AddCommGroup (Sect l)] [∀ l, Module K (Sect l)] {N n : ℕ}
    (D : Degeneration Berk K Sect N n)
    (hVI : ∀ l : ℕ, ∃ (m : ℕ) (θ : Module.Basis (Fin m) K (Sect l)),
      D.ValuativeIndependent l θ)
    (φ₀ : Berk → ℝ) (hφ₀ : D.IsNACYPotential φ₀) :
    D.WeakComparisonProperty φ₀ := by sorry

/-! ### Milestones: the `c`-transform (§3.2) -/

end ValuativeSYZ
