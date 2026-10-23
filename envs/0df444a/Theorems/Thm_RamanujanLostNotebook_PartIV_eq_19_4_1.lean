-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_eq_19_4_1
-- name    : RamanujanLostNotebook.PartIV.eq_19_4_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T15:41:06.772377+00:00
-- url     : https://prove2.me/theorems/7f9b71a3-4335-4008-841d-d18443c74f07
-- title:
--   Ramanujan's symmetric double-integral formula with ζ(1−s), ζ(−s)
-- statement:
--   Let $s\in\mathbb{C}$ with $\mathrm{Re}\,s>-1$, $\cos(\pi s/2)\ne0$, $\sin(\pi s/2)\ne0$, and let $\alpha,\beta>0$ with $\alpha\beta=4\pi^2$. Put $G(\alpha)=\frac{\zeta(1-s)}{4\cos(\pi s/2)}\alpha^{(s-1)/2}+\frac{\zeta(-s)}{8\sin(\pi s/2)}\alpha^{(s+1)/2}+\alpha^{(s+1)/2}\int_0^\infty\!\!\int_0^\infty\frac{x^s\sin(\alpha xy)}{(e^{2\pi x}-1)(e^{2\pi y}-1)}\,dx\,dy$. Then $G(\alpha)=G(\beta)$. Differs from the printed source: the non-vanishing of $\cos(\pi s/2)$ and $\sin(\pi s/2)$ is added by us.
--
--   **Discrepancy from the printed source.** Book p. 379, (19.4.1): stated for Re s > −1 with no exclusions. We add cos(πs/2) ≠ 0 and sin(πs/2) ≠ 0 (odd integers and even integers s, in particular s = 0 where ζ(1−s) has its pole): there the individual terms are undefined. Numerical agreement to 30–40 digits at five points (numerical evidence, not a proof). Restriction added by us. Audit (Codex, independent mpmath): confirms that at s = 0 both trigonometric denominators vanish and ζ(1−s) has its pole, and that the exclusions are needed; its values G(1) = G(4π²) = −0.55231401336414760712201741329507773 at s = 1/2 and G(0.2) = G(4π²/0.2) = 0.0026062410936404771686932202078942661 at s = 5/2 coincide with ours.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 19, Theorem 19.4.1, p. 379, eq. (19.4.1).

import Mathlib
open MeasureTheory

namespace RamanujanLostNotebook.PartIV
theorem eq_19_4_1 (s : ℂ) (hs : -1 < s.re)
    (hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0)
    (hsin : Complex.sin ((Real.pi : ℂ) * s / 2) ≠ 0)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : α * β = 4 * Real.pi ^ 2) :
    riemannZeta (1 - s) / (4 * Complex.cos ((Real.pi : ℂ) * s / 2))
          * ((α : ℝ) : ℂ) ^ ((s - 1) / 2)
        + riemannZeta (-s) / (8 * Complex.sin ((Real.pi : ℂ) * s / 2))
          * ((α : ℝ) : ℂ) ^ ((s + 1) / 2)
        + ((α : ℝ) : ℂ) ^ ((s + 1) / 2)
          * (∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
              (x : ℂ) ^ s * ((Real.sin (α * x * y)
                / ((Real.exp (2 * Real.pi * x) - 1) * (Real.exp (2 * Real.pi * y) - 1)) : ℝ) : ℂ))
      = riemannZeta (1 - s) / (4 * Complex.cos ((Real.pi : ℂ) * s / 2))
          * ((β : ℝ) : ℂ) ^ ((s - 1) / 2)
        + riemannZeta (-s) / (8 * Complex.sin ((Real.pi : ℂ) * s / 2))
          * ((β : ℝ) : ℂ) ^ ((s + 1) / 2)
        + ((β : ℝ) : ℂ) ^ ((s + 1) / 2)
          * (∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
              (x : ℂ) ^ s * ((Real.sin (β * x * y)
                / ((Real.exp (2 * Real.pi * x) - 1) * (Real.exp (2 * Real.pi * y) - 1)) : ℝ) : ℂ)) := by sorry
end RamanujanLostNotebook.PartIV
