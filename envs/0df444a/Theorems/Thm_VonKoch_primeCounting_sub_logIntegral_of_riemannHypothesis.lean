-- Prove2me | Theorems.Thm_VonKoch_primeCounting_sub_logIntegral_of_riemannHypothesis
-- name    : VonKoch.primeCounting_sub_logIntegral_of_riemannHypothesis
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:37:12.402188+00:00
-- url     : https://prove2.me/theorems/7bac9282-5bf9-4ad5-afbf-cbe69ac25993
-- title:
--   von Koch: under RH, $\pi(x)=\operatorname{Li}(x)+O(\sqrt{x}\log x)$
-- statement:
--   Assume the Riemann hypothesis, in Mathlib's form `RiemannHypothesis`. Then there is a constant $C$ such that for all real $x\ge3$
--
--   $$\left|\pi(x)-\operatorname{Li}(x)\right|\le C\sqrt{x}\,\log x,\qquad \operatorname{Li}(x)=\int_2^x\frac{dt}{\log t},$$
--
--   where $\pi(x)$ is the number of primes $\le x$. This is von Koch's theorem (1901): under RH the prime number theorem holds with error $O(\sqrt x\log x)$. Von Koch also proved the converse; it is not part of this statement.
--
--   **Formalization Note.** $\pi(x)$ is `Nat.primeCounting ⌊x⌋₊`. The offset logarithmic integral $\operatorname{Li}(x)=\int_2^x dt/\log t$ is written as an interval integral. It differs from $\mathrm{li}(x)$ by the constant $\mathrm{li}(2)$, which is absorbed in the $O$-term. The bound is explicit in $x$ with a single constant $C$, valid for every $x\ge3$.
-- source:
--   H. von Koch, Sur la distribution des nombres premiers, Acta Math. 24 (1901), 159–182. E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed. (rev. D. R. Heath-Brown), OUP 1986, §14.26 (consequences of RH for π(x)); H. L. Montgomery and R. C. Vaughan, Multiplicative Number Theory I, Cambridge Univ. Press 2007, Theorem 13.1 (RH ⇒ ψ(x) = x + O(x^{1/2} log² x) and π(x) = li(x) + O(x^{1/2} log x)).

import Mathlib

namespace VonKoch

theorem primeCounting_sub_logIntegral_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ x : ℝ, 3 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤
        C * Real.sqrt x * Real.log x := by sorry

end VonKoch
