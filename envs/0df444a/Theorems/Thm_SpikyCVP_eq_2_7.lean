-- Prove2me | Theorems.Thm_SpikyCVP_eq_2_7
-- name    : SpikyCVP.eq_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:43:59.880158+00:00
-- url     : https://prove2.me/theorems/635c8837-edb1-4676-b7a1-c29930958a2d
-- title:
--   Equation (2.7) — the Laplace transform of the positive stable density $g_\alpha$
-- statement:
--   Let $0<\alpha<1$ (that is, $\alpha=p/2$ with $0<p<2$), and let $g_\alpha$ be the function of Equation (2.11). Then $g_\alpha(a)\ge0$ for every $a$, and for every $y\ge0$
--
--   $$\exp\big(-y^{\alpha}\big)=\int_0^\infty \exp(-ay)\,g_\alpha(a)\,da .$$
--
--   In particular $g_\alpha$ is a probability density on $(0,\infty)$ (take $y=0$). Substituting $y=(x/r)^2$ and $a=\pi r^2/s^2$ writes $e^{-|x|^p/r^p}$ as a mixture of Gaussians $e^{-\pi x^2/s^2}$ over widths $s$, which is the basis of the whole algorithm.
--
--   Differences from the source:
--   - reading: g_{p/2} is the density of the positive p/2-stable law given by Bernstein's theorem, and (2.11) is derived from Zolotarev's (2.10) → g_α is defined by the formula (2.11), and the statement asserts that it is nonnegative and satisfies (2.7); reason: defining the density abstractly would hide an existence claim in a definition; the statement carries the cited facts of Bernstein and Zolotarev together
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Equation (2.7), p.13 (PDF p.15), for g_α of Equation (2.11), p.13

import Mathlib
import Definitions.Def_SpikyCVP_gStable

open MeasureTheory

namespace SpikyCVP

/-- **Equation (2.7): the Laplace transform of the positive stable density.**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Equation (2.7), p.13 (PDF p.15), for the density `gα` of Equation (2.11), p.13.

For `0 < α < 1` (that is, `α = p/2` with `0 < p < 2`), the function `gα` of (2.11) is nonnegative, and for
every `y ≥ 0`, `exp(−y^α) = ∫_0^∞ exp(−ay) gα(a) da`.

**Formalization Note.** The paper obtains `g_{p/2}` from Bernstein's theorem and derives (2.11) from
Zolotarev's (2.10); here (2.11) defines `gα`, so this statement also carries those two cited facts. The
left side is positive, so the identity cannot hold through a junk value of the integral. -/
theorem eq_2_7 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ a, 0 ≤ gStable α a) ∧
    ∀ y : ℝ, 0 ≤ y →
      Real.exp (-(y ^ α)) = ∫ a in Set.Ioi (0 : ℝ), Real.exp (-(a * y)) * gStable α a := by sorry

end SpikyCVP
