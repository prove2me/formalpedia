-- Prove2me | Theorems.Thm_ValuativeSYZ_thm_4_5_kantorovich_bound
-- name    : ValuativeSYZ.thm_4_5_kantorovich_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T12:51:41.626554+00:00
-- url     : https://prove2.me/theorems/5437a725-4e31-41ab-8878-a649bad3f2b2
-- title:
--   Theorem 4.5, duality bound: $\int c\,d\pi \le \int \varphi^c d\nu + \int \varphi\, d\mu$
-- statement:
--   **Theorem 4.5, duality bound.** The non-archimedean Monge–Ampère equation is the Kantorovich dual
--   of an optimal transport problem between the essential skeleton, carrying the measure $\mu$, and the
--   space $B_y$ of limiting tropical theta functions, carrying the measure $\nu$ built from the Lebesgue
--   measure of the Okounkov body: the solution restricted to the skeleton is the minimiser of
--   $$F_\mu(\varphi) \;=\; \int_{B_y}\varphi^{c}\,d\nu \;+\; \int_{\mathrm{Sk}(X)}\varphi\,d\mu .$$
--
--   This milestone records the inequality that makes $F_\mu$ a dual functional, which is the elementary
--   half of the duality: from the definition of the $c$-transform one has $c(x,p) \le \varphi(x) +
--   \varphi^{c}(p)$ pointwise, hence for **every** coupling $\pi$ of $\mu$ and $\nu$,
--   $$\int c \, d\pi \;\le\; \int \varphi^{c}\,d\nu + \int \varphi\,d\mu .$$
--   So every admissible potential gives an upper bound for the transport cost of every coupling; the
--   hard half, that the bound is attained by the Monge–Ampère solution, is not part of this milestone.
-- source:
--   Yang Li, *Valuative independence and metric SYZ conjecture*, arXiv:2605.00516v1 (1 May 2026), https://arxiv.org/abs/2605.00516, pp. 36, Theorem 4.5 (the Kantorovich duality bound for the functional $F_\mu$)

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

set_option autoImplicit false

open MeasureTheory

namespace ValuativeSYZ

/-- **Theorem 4.5, duality bound.** For every bounded measurable potential `φ` and every
coupling `π` of the measures `μ` on the skeleton and `ν` on the parameter space, the transport
cost of `π` is dominated by the value `∫ φᶜ dν + ∫ φ dμ` of the functional `F_μ` at `φ`. -/
theorem thm_4_5_kantorovich_bound {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    [Nonempty X] (c : X → B → ℝ) (M : ℝ) (hc : ∀ x p, |c x p| ≤ M)
    (hcmeas : Measurable fun z : X × B => c z.1 z.2)
    (φ : X → ℝ) (hφ : ∀ x, |φ x| ≤ M) (hφmeas : Measurable φ)
    (htmeas : Measurable (ctransform c φ))
    (μ : Measure X) (ν : Measure B) (π : Measure (X × B))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure π]
    (hπ₁ : π.map Prod.fst = μ) (hπ₂ : π.map Prod.snd = ν) :
    ∫ z, c z.1 z.2 ∂π ≤ (∫ p, ctransform c φ p ∂ν) + ∫ x, φ x ∂μ := by sorry

end ValuativeSYZ
