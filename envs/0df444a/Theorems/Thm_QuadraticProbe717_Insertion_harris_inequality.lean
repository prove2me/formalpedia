-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_harris_inequality
-- name    : QuadraticProbe717.Insertion.harris_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:00.187594+00:00
-- url     : https://prove2.me/theorems/421d6fe2-96db-46d7-bddb-8a57c1509f25
-- title:
--   Theorem 2.2 — Harris’s inequality
-- statement:
--   Let $Y_1,\ldots,Y_s$ be independent measurable real random variables on any probability space. Let $f,g:\mathbb R^s\to\mathbb R$ be either both coordinatewise nondecreasing or both coordinatewise nonincreasing. If $f(Y)$, $g(Y)$ and their product are integrable, then
--   $$\operatorname{Cov}(f(Y),g(Y))\ge0.$$
--   This is the general Harris inequality needed for unbounded Poisson inputs; it does not restrict the inputs to bits or to identical distributions.
--
--   Differences from the source:
--   - encoding: finite real random variables and covariance whenever defined → Fin indices on any probability space, with both tests and their product integrable; reason: this states covariance existence without boundedness, identical laws, or square-integrability
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Theorem 2.2, p. 5 (PDF p. 5)

import Definitions.Def_QuadraticProbe717_Insertion_association

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem harris_inequality {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : ℕ) (Y : Fin s → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (f g : (Fin s → ℝ) → ℝ)
    (hmono : (Monotone f ∧ Monotone g) ∨ (Antitone f ∧ Antitone g))
    (hex : CovarianceExists P (fun ω => f (fun i => Y i ω))
      (fun ω => g (fun i => Y i ω))) :
    0 ≤ covariance (fun ω => f (fun i => Y i ω)) (fun ω => g (fun i => Y i ω)) P := by sorry

end QuadraticProbe717.Insertion
