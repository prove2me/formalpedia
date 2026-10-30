-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_entry_6_2_2
-- name    : RamanujanLostNotebook.PartIV.entry_6_2_2
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-06T12:43:36.810434+00:00
-- url     : https://prove2.me/theorems/f63628a4-6e0c-4fa9-93bf-d7a8d01006cb
-- title:
--   Integral with a lacunary series giving psi(a/b+c) - log(a/b)
-- statement:
--   Let $a,b,c>0$ with $b>1$ and $\psi=\Gamma'/\Gamma$. The function $x\mapsto\Big(\frac{x^{c-1}}{1-x}-\frac{b x^{bc-1}}{1-x^{b}}\Big)\sum_{k=0}^{\infty}x^{ab^{k}}$ is integrable on $(0,1)$ and its integral over $(0,1)$ equals $\psi\!\big(\tfrac ab+c\big)-\log\tfrac ab$. Differs from the printed source: the book (p. 154, Entry 6.2.2, unnumbered display) prints only the equality of the integral with psi(a/b + c) - log(a/b); this statement also concludes that the integrand is integrable on (0,1), so that the equality cannot hold through the value 0 that Lean gives a non-integrable integral. Evidence for the added conclusion: an analytic sketch (the first factor stays bounded at x = 1 and the lacunary series grows only logarithmically there) and numerical agreement to at least 38 digits at five parameter triples; numerical evidence, not a proof. The addition was made by us (the formalizers), not by the book's authors.
--
--   **Discrepancy from the printed source.** Book, p. 154, Entry 6.2.2 (unnumbered display): for a, b, c > 0 with b > 1 the integral over (0,1) of (x^(c-1)/(1-x) - b x^(bc-1)/(1-x^b)) sum_{k>=0} x^(a b^k) equals psi(a/b + c) - log(a/b); nothing is said about integrability. We state: the same equality with the same hypotheses, preceded by the extra conclusion IntervalIntegrable (integrand) volume 0 1. Reason: psi(a/b + c) = log(a/b) has solutions, and Lean assigns 0 to the integral of a non-integrable function. Evidence: analytic sketch only (the first factor tends to (b-1)(c-1/2) at x = 1, the series grows like log(1/(1-x))/log b), plus quadrature agreeing with the closed form to 5e-39 or better at (a,b,c) = (1,2,1), (0.3,1.5,2.2), (0.05,1.05,0.03), (7,5,0.4), (3,1.02,50); the independent audit checked the book's telescoping partial sums at four of these points. Numerical evidence, not a proof. The formula itself is unchanged. Change made by us (the formalizers), not by the book's authors.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 6, Entry 6.2.2, p. 154.

import Mathlib
open MeasureTheory

namespace RamanujanLostNotebook.PartIV
theorem entry_6_2_2 (a b c : ℝ) (ha : 0 < a) (hb : 1 < b) (hc : 0 < c) :
    IntervalIntegrable
        (fun x : ℝ =>
          (x ^ (c - 1) / (1 - x) - b * x ^ (b * c - 1) / (1 - x ^ b))
            * ∑' k : ℕ, x ^ (a * b ^ k))
        MeasureTheory.volume 0 1 ∧
      (∫ x in (0 : ℝ)..1,
          (x ^ (c - 1) / (1 - x) - b * x ^ (b * c - 1) / (1 - x ^ b))
            * ∑' k : ℕ, x ^ (a * b ^ k))
        = logDeriv Real.Gamma (a / b + c) - Real.log (a / b) := by sorry
end RamanujanLostNotebook.PartIV
