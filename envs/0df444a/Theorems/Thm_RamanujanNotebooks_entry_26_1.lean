-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_26_1
-- name    : RamanujanNotebooks.entry_26_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T22:20:56.018101+00:00
-- url     : https://prove2.me/theorems/09f55825-de90-43b8-a323-447119a05d60
-- title:
--   Lemniscate inversion: mu^2/(2v^2) as csc^2(theta) - 1/pi - 8 sum n cos(2n theta)/(e^(2 pi n) - 1)
-- statement:
--   Let $\mu$ be defined by $\frac{\pi}{2}\cdot\frac{\mu}{\sqrt2}=\int_0^1\frac{dt}{\sqrt{1-t^4}}$, and let $0<\theta\le\pi/2$, $0\le v\le1$ satisfy $\frac{\theta\mu}{\sqrt2}=\int_0^v\frac{dt}{\sqrt{1-t^4}}$. Then $$\frac{\mu^2}{2v^2}=\frac1{\sin^2\theta}-\frac1\pi-8\sum_{n=1}^\infty\frac{n\cos(2n\theta)}{e^{2\pi n}-1},$$ the series converging absolutely.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part IV (Springer, 1994), Chapter 26, Entry 1, p. 247, eq. (1.1), (1.2).

import Mathlib

namespace RamanujanNotebooks
theorem entry_26_1 (θ v μ : ℝ)
    (hμ : μ * (Real.pi / 2) / Real.sqrt 2 = ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - t ^ 4))
    (hθv : θ * μ / Real.sqrt 2 = ∫ t in (0 : ℝ)..v, 1 / Real.sqrt (1 - t ^ 4))
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi / 2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * Real.cos (2 * ((n : ℝ) + 1) * θ) /
        (Real.exp (2 * Real.pi * ((n : ℝ) + 1)) - 1))
      ((1 / Real.sin θ ^ 2 - 1 / Real.pi - μ ^ 2 / (2 * v ^ 2)) / 8) := by sorry
end RamanujanNotebooks
