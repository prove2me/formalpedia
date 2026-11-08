-- Prove2me | Theorems.Thm_ScutaruFid_kernel_coeffs_of_cov
-- name    : ScutaruFid.kernel_coeffs_of_cov
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:56:04.988608+00:00
-- url     : https://prove2.me/theorems/e397b9e0-09bf-4b59-90c6-95eb8d33bb35
-- title:
--   Eqs. (12)–(13): the kernel coefficients recovered from the matrix $A$
-- statement:
--   Let $a\in\mathbb C$ and $b\in\mathbb R$ with $\operatorname{Re}a+b>0$, put $d=\bar a$ and define, as in (11),
--
--   $$
--   a_{qq}=\frac{1}{a+d+2b},\qquad a_{pp}=\frac{4(ad-b^2)}{a+d+2b},\qquad a_{pq}=\frac{i(a-d)}{a+d+2b}.
--   $$
--
--   Then $a_{qq},a_{pp},a_{pq}$ are real, and with $\det A=a_{qq}a_{pp}-a_{pq}^2$,
--
--   $$
--   a=\frac{\det A+1}{4a_{qq}}-i\frac{a_{pq}}{2a_{qq}},\qquad b=-\frac{\det A-1}{4a_{qq}} .
--   $$
--
--   So the kernel coefficients of a Gaussian state are functions of its matrix $A$; this is how `stateKernel A u` parametrizes every Gaussian state by $(A,u)$.
--
--   Differences from the source:
--   - generalization: b with −b ≥ 0 (the standing Re a ≥ −b ≥ 0) → any real b with Re a + b > 0; reason: the identities are algebraic and need only a + ā + 2b ≠ 0; the source's case is included
--   - encoding: d = ā stated with (13) → d replaced by ā from the start; reason: Hermiticity (density_kernel_conditions) gives d = ā; the inversion is stated for that d
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eqs. (11)–(13), p.2

import Mathlib

namespace ScutaruFid

/-- **Kernel coefficients from the covariance matrix**, eqs. (11)–(13). Scutaru,
arXiv:quant-ph/9708013v1, p.2: "a_qq = 2(<Q²> − <Q>²) = 1/(a + d + 2b),
a_pp = 2(<P²> − <P>²) = 4(ad − b²)/(a + d + 2b), a_pq = … = i(a − d)/(a + d + 2b) (11) … If A is the
matrix (a_qq a_pq; a_pq a_pp) and detA = a_qq a_pp − a_pq² it is easy to show that
a = (detA + 1)/(4a_qq) − i a_pq/(2a_qq) (12) d = ā and b = −(detA − 1)/(4a_qq) (13)".

For `a ∈ ℂ` and real `b` with `Re a + b > 0`, put `d = ā` and define `a_qq, a_pp, a_pq` by (11).
Then all three are real, and with `det A = a_qq a_pp − a_pq²` the coefficients are recovered by
(12) and (13).

**Formalization Note** Pure algebra in `ℂ`; reality of `a_qq, a_pp, a_pq` is stated as vanishing
imaginary parts. The page's standing `−b ≥ 0` is not needed and not assumed. -/
theorem kernel_coeffs_of_cov (a : ℂ) (b : ℝ) (hab : 0 < a.re + b) :
    let s : ℂ := a + star a + 2 * (b : ℂ)
    let aqq : ℂ := 1 / s
    let app : ℂ := 4 * (a * star a - (b : ℂ) ^ 2) / s
    let apq : ℂ := Complex.I * (a - star a) / s
    let detA : ℂ := aqq * app - apq ^ 2
    aqq.im = 0 ∧ app.im = 0 ∧ apq.im = 0 ∧
      a = (detA + 1) / (4 * aqq) - Complex.I * apq / (2 * aqq) ∧
      (b : ℂ) = -(detA - 1) / (4 * aqq) := by sorry

end ScutaruFid
