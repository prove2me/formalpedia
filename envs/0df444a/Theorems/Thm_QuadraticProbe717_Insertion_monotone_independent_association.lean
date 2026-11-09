-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_monotone_independent_association
-- name    : QuadraticProbe717.Insertion.monotone_independent_association
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:23.756725+00:00
-- url     : https://prove2.me/theorems/3b90eb3c-16b0-48b1-b060-2152ca9b2a2f
-- title:
--   Corollary 2.3 — monotone independent association
-- statement:
--   Let $Y_1,\ldots,Y_s$ be independent measurable real random variables. Let $f_1,\ldots,f_t:\mathbb R^s\to\mathbb R$ be jointly coordinatewise nondecreasing, or jointly coordinatewise nonincreasing. Define $X_i=f_i(Y)$. Then
--   $$ (X_i)_{i=1}^t\text{ is positively associated}.$$
--   Positive association quantifies over all increasing tests whose covariance exists. In particular, no boundedness or square-integrability is imposed on the independent inputs.
--
--   Differences from the source:
--   - encoding: finite real random variables and covariance whenever defined → Fin indices on any probability space, with both tests and their product integrable; reason: this states covariance existence without boundedness, identical laws, or square-integrability
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Corollary 2.3, p. 5 (PDF p. 5)

import Definitions.Def_QuadraticProbe717_Insertion_association

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem monotone_independent_association {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s t : ℕ)
    (Y : Fin s → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (f : Fin t → (Fin s → ℝ) → ℝ)
    (hmono : (∀ i, Monotone (f i)) ∨ (∀ i, Antitone (f i))) :
    PositivelyAssociated P (fun i ω => f i (fun j => Y j ω)) := by sorry

end QuadraticProbe717.Insertion
