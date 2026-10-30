-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_central_monomial_coefficient_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.central_monomial_coefficient_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:13:36.366984+00:00
-- url     : https://prove2.me/theorems/2b620d62-c08c-4900-a06f-ca1fbec80fc3
-- title:
--   Lemma 5.9
-- statement:
--   Let $\mu\vdash w$ with $w\ge1$, and suppose the identity of observables $\prod_{i=1}^{\ell(\mu)}p_{\mu_i}^\sharp=\sum_\nu c_\nu p_\nu^\sharp$ holds with finitely many complex coefficients. Then
--
--   $$|c_\nu|\le4^{w^2\log w}\qquad\text{for every }\nu.$$
--
--   Equality is required on all Young diagrams. At $w=1$ the bound is one. This controls coefficients when single-cycle monomials are expanded in the central-character basis.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 51, Lemma 5.9

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 5.9, arXiv:1501.05028v1, PDF p.51. Visually verified the exponent w² log w. A pointwise equality at one diagram would not determine coefficients. -/
theorem central_monomial_coefficient_bound
    (mu : YoungDiagram) (hmu : 0 < mu.card) (a : YoungDiagram →₀ ℂ)
    (ha : ∀ lambda : YoungDiagram, (sharpMonomial mu lambda : ℂ) = complexObservable a lambda) :
    ∀ nu : YoungDiagram,
      ‖a nu‖ ≤ Real.rpow 4 ((mu.card : ℝ)^2 * Real.log mu.card) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
