-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_16_1_5
-- name    : RamanujanLostNotebook.PartI.entry_16_1_5
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:26:32.156735+00:00
-- url     : https://prove2.me/theorems/4f0bc58d-6b78-4455-86d0-636276d24a48
-- title:
--   Fourier Gaussian integral of two reciprocal products
-- statement:
--   Let a,b be complex, m,k real, k nonzero and |a|,|b|<1. Put q=exp(-2k^2), with (z;q)_infinity=product over j>=0 of (1-z q^j) and (q;q)_n=product over j=1,...,n of (1-q^j). The function f(x)=exp(-x^2+2mx)/[(a exp(-k^2+2ikx);q)_infinity(b exp(-k^2-2ikx);q)_infinity] is absolutely integrable. Both its denominator product at every real x and (abq;q)_infinity are nonzero, and its integral equals sqrt(pi) exp(m^2)(-a exp(-2k^2+2imk);q)_infinity(-b exp(-2k^2-2imk);q)_infinity/(abq;q)_infinity. Differs from the printed source: we exclude k=0, allowed by the printed real-k hypothesis, because q=exp(-2k^2)=1 is outside the analytic q-product domain. The formula itself is unchanged; absolute integrability and both pointwise and right-side denominator nonvanishing are conclusions. This exclusion is ours, not an editorial correction.
--
--   **Discrepancy from the printed source.** Differs from the printed source: we exclude k=0, allowed by the printed real-k hypothesis, because q=exp(-2k^2)=1 is outside the analytic q-product domain. The formula itself is unchanged; absolute integrability and both pointwise and right-side denominator nonvanishing are conclusions. This exclusion is ours, not an editorial correction.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 16, Entry 16.1.5, p. 368, eq. (16.1.7).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPochInf
open MeasureTheory
open scoped BigOperators

namespace RamanujanLostNotebook.PartI
theorem entry_16_1_5 (a b : ℂ) (m k : ℝ) (hk : k ≠ 0)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    let q : ℂ := (Real.exp (-2 * k ^ 2) : ℂ)
    let f : ℝ → ℂ := fun x =>
      (Real.exp (-(x ^ 2) + 2 * m * x) : ℂ) / (qPochInf (a * Complex.exp (-((k : ℂ) ^ 2) + 2 * Complex.I * (k : ℂ) * (x : ℂ))) q * qPochInf (b * Complex.exp (-((k : ℂ) ^ 2) - 2 * Complex.I * (k : ℂ) * (x : ℂ))) q)
    Integrable f ∧ (∀ x : ℝ,
        (qPochInf (a * Complex.exp (-((k : ℂ) ^ 2) + 2 * Complex.I * (k : ℂ) * (x : ℂ))) q *
          qPochInf (b * Complex.exp (-((k : ℂ) ^ 2) - 2 * Complex.I * (k : ℂ) * (x : ℂ))) q) ≠ 0) ∧
      qPochInf (a * b * q) q ≠ 0 ∧
      (∫ x : ℝ, f x) =
        (Real.sqrt Real.pi : ℂ) * (Real.exp (m ^ 2) : ℂ) * qPochInf (-a * Complex.exp (-2 * (k : ℂ) ^ 2 + 2 * Complex.I * (m : ℂ) * (k : ℂ))) q * qPochInf (-b * Complex.exp (-2 * (k : ℂ) ^ 2 - 2 * Complex.I * (m : ℂ) * (k : ℂ))) q / qPochInf (a * b * q) q := by sorry
end RamanujanLostNotebook.PartI
