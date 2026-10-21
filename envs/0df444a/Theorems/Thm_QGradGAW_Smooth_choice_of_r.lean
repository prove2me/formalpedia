-- Prove2me | Theorems.Thm_QGradGAW_Smooth_choice_of_r
-- name    : QGradGAW.Smooth.choice_of_r
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:31.717171+00:00
-- url     : https://prove2.me/theorems/12074a09-f435-441b-adee-0641e82ec5f3
-- title:
--   Proof of Theorem 25, p. 29 — r⁻¹ := 9cm√d (81·8·42πcm√d/ε)^{1/(2m)} gives Σ_{k≥2m+1} (8rcm√d)ᵏ ≤ εr/(8·42π)
-- statement:
--   Let $d,m\ge1$ be integers and $0<\varepsilon\le c$. Put
--   $$A=\frac{81\cdot8\cdot42\pi\,c\,m\sqrt d}{\varepsilon},\qquad r^{-1}=9\,c\,m\sqrt d\;A^{1/(2m)} .$$
--   Then $8rcm\sqrt d=\tfrac89\,A^{-1/(2m)}$ and
--   $$\sum_{k=2m+1}^{\infty}\big(8rcm\sqrt d\big)^k\;\le\;\frac{\varepsilon r}{8\cdot42\pi}.$$
--
--   With this edge length $r$, the error bound of Theorem 24 meets the accuracy $\varepsilon r/(8\cdot 42\pi)$ required by Theorem 21, which is how the two are combined in the proof of Theorem 25.
-- source:
--   Gilyén, Arunachalam, Wiebe, Optimizing quantum optimization algorithms via faster quantum gradient computation, arXiv:1711.00465v3, p. 29, proof of Theorem 25 (the choice of r and the chain of inequalities after it)

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

namespace QGradGAW.Smooth

/-- arXiv:1711.00465v3, p. 29, proof of Theorem 25 (the choice of `r`): for `d, m ∈ ℕ₊` and
`0 < ε ≤ c`, put `A := 81 · 8 · 42π c m √d / ε` and `r⁻¹ := 9 c m √d A^{1/(2m)}`. Then
`8 r c m √d = (8/9) A^{−1/(2m)}` and `Σ_{k=2m+1}^∞ (8 r c m √d)^k ≤ ε r / (8 · 42π)`. -/
theorem choice_of_r (d m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) (c ε : ℝ) (hε : 0 < ε) (hεc : ε ≤ c) :
    let A : ℝ := 81 * 8 * 42 * Real.pi * c * m * Real.sqrt d / ε
    let r : ℝ := 1 / (9 * c * m * Real.sqrt d * A ^ (1 / (2 * (m : ℝ))))
    8 * r * c * m * Real.sqrt d = 8 / 9 * A ^ (-(1 / (2 * (m : ℝ)))) ∧
      ∑' k : ℕ, (8 * r * c * m * Real.sqrt d) ^ (2 * m + 1 + k) ≤ ε * r / (8 * 42 * Real.pi) := by sorry

end QGradGAW.Smooth
