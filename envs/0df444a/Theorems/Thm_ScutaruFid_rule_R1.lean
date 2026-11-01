-- Prove2me | Theorems.Thm_ScutaruFid_rule_R1
-- name    : ScutaruFid.rule_R1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:57.770524+00:00
-- url     : https://prove2.me/theorems/64b64b7d-af9a-4537-918d-45701ef7ffb3
-- title:
--   Rule R1, eq. (5): composition of Gaussian kernels (corrected: $(k_1+l_2)^2$ in $G$)
-- statement:
--   Let $a_j,b_j,d_j,l_j,k_j,g_j\in\mathbb C$ ($j=1,2$) with $\operatorname{Re}(d_1+a_2)>0$, and write $c=d_1+a_2$. For all real $x,y$,
--
--   $$
--   \int_{-\infty}^{+\infty}e^{-(a_1x^2+d_1z^2+2b_1xz)+l_1x+k_1z+g_1}\,e^{-(a_2z^2+d_2y^2+2b_2zy)+l_2z+k_2y+g_2}\,dz
--   =e^{-(Ax^2+Dy^2+2Bxy)+Lx+Ky+G}
--   $$
--
--   with
--
--   $$
--   A=a_1-\frac{b_1^2}{c},\quad D=d_2-\frac{b_2^2}{c},\quad B=-\frac{b_1b_2}{c},\quad L=l_1-\frac{(k_1+l_2)b_1}{c},\quad K=k_2-\frac{(k_1+l_2)b_2}{c},
--   $$
--   $$
--   G=g_1+g_2+\frac{(k_1+l_2)^2}{4c}+\ln\sqrt{\frac{\pi}{c}} .
--   $$
--
--   Rule R1 is the multiplication law of the oscillator semigroup in the kernel parameters; the paper inverts it to obtain square roots (rule R2) and applies it twice to compute the fidelity.
--
--   **Formalization Note** $\ln\sqrt{\pi/c}$ is written $\tfrac12\log(\pi/c)$ with the principal complex logarithm; for $\operatorname{Re}c>0$ this is the logarithm of the principal square root.
--
--   Differences from the source:
--   - correction: G = g1 + g2 + (k1 + l2)/(4(d1 + a2)) + ln √(π/(d1 + a2)) → G = g1 + g2 + (k1 + l2)²/(4(d1 + a2)) + ½ log(π/(d1 + a2)); reason: completing the square in ∫ exp(−(d1+a2)z² + (k1+l2−2b1x−2b2y)z) dz gives (k1+l2)²; with a1 = d1 = a2 = d2 = ½, k1 = 2 and all other parameters 0, the integral at x = y = 0 is √π·e, so G = 1 + ½ ln π, while the printed G is ½ + ½ ln π
--   - generalization: parameters of two Gaussian density operators → any complex parameters with Re(d1 + a2) > 0; reason: the Gaussian integral needs only convergence; for density operators Re d1 > 0 and Re a2 > 0 (Re a ≥ −b ≥ 0 with Re a + b > 0), so the source's case is included
--   - encoding: ln √(π/(d1 + a2)) → ½ · Complex.log(π/(d1 + a2)) (principal branch); reason: same value for Re(d1 + a2) > 0
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eq. (5), p.1

import Mathlib
import Definitions.Def_ScutaruFid_gaussKernel

namespace ScutaruFid

/-- **Rule R1: composition of Gaussian kernels**, eq. (5) (corrected: `(k₁ + l₂)²` in `G`).
Scutaru, arXiv:quant-ph/9708013v1, eq. (5), p.1: "Let us denote by A, B, D, L, K and G the
corresponding parameters of the Gaussian <x|ρ1ρ2|y>. Then the semigroup composition law (the rule
R1) is given by A = a1 − b1²/(d1 + a2), D = d2 − b2²/(d1 + a2), B = −b1b2/(d1 + a2),
L = l1 − (k1 + l2)b1/(d1 + a2), K = k2 − (k1 + l2)b2/(d1 + a2),
G = g1 + g2 + (k1 + l2)/(4(d1 + a2)) + ln √(π/(d1 + a2))".

For complex parameters with `Re(d₁ + a₂) > 0` and all real `x, y`,
`∫ K₁(x, z) K₂(z, y) dz = exp[−(Ax² + Dy² + 2Bxy) + Lx + Ky + G]` with `A, B, D, L, K` as printed
and `G = g₁ + g₂ + (k₁ + l₂)²/(4(d₁ + a₂)) + ½ log(π/(d₁ + a₂))`.

**Formalization Note** The page prints `(k₁ + l₂)` unsquared in `G`; completing the square gives
`(k₁ + l₂)²`. `ln √(π/c)` is written `½ log(π/c)` with the principal complex logarithm (for
`Re c > 0` this is the logarithm of the principal square root). -/
theorem rule_R1 (a₁ b₁ d₁ l₁ k₁ g₁ a₂ b₂ d₂ l₂ k₂ g₂ : ℂ) (hc : 0 < (d₁ + a₂).re) (x y : ℝ) :
    let c := d₁ + a₂
    (∫ z : ℝ, gaussKernel a₁ b₁ d₁ l₁ k₁ g₁ x z * gaussKernel a₂ b₂ d₂ l₂ k₂ g₂ z y) =
      gaussKernel (a₁ - b₁ ^ 2 / c) (-(b₁ * b₂) / c) (d₂ - b₂ ^ 2 / c)
        (l₁ - (k₁ + l₂) * b₁ / c) (k₂ - (k₁ + l₂) * b₂ / c)
        (g₁ + g₂ + (k₁ + l₂) ^ 2 / (4 * c) + (1 / 2) * Complex.log ((Real.pi : ℂ) / c)) x y := by sorry

end ScutaruFid
