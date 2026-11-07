-- Prove2me | Theorems.Thm_TwoBoxMemory_eq_B15_rational_separation
-- name    : TwoBoxMemory.eq_B15_rational_separation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:10.761113+00:00
-- url     : https://prove2.me/theorems/bed82c86-822a-4e73-a856-8e561c270887
-- title:
--   (B.15) — rational parameters are exponentially separated
-- statement:
--   Let $r=r_1/r_2$, $s=s_1/s_2$, $\beta=b_1/b_2$ be rationals in lowest positive terms such that $(r,s,\beta,D)$ is a non-tie positive saddle with irrational logarithmic failure ratio, with saddle cost $C=Dv/u$ and greedy word $W$, and put $Z=\max(r_2,s_2)$. Then $Z>1$,
--
--   $$|\beta r^i-s^j|\ \ge\ \frac{1}{b_2Z^{i+j}}\qquad(i,j\ge0),$$
--
--   and for every $M\ge1$
--
--   $$\Delta_M\ \ge\ \frac{G}{2b_2}Z^{-F_M}\ \ge\ \frac{G}{2b_2}Z^{-2H_M} .$$
--
--   This is case (i) of Theorem B.4: rational parameters satisfy the separation hypothesis.
--
--   Differences from the source:
--   - encoding: lowest positive terms r = r_1/r_2, s = s_1/s_2, β = b_1/b_2 → r, s, β : ℚ with denominators Rat.den; reason: Rat stores the reduced fraction with positive denominator
--   - encoding: $\Delta_M=V_M-V$ with $V_M,V\in[0,\infty]$ → `gap` $=(V_M).\mathrm{toReal}-V.\mathrm{toReal}$; reason: both values are finite for $M\ge1$ (proved in the verification file), so the real difference is exact
--   - encoding: controller risk as the risk (B.4) of the cylinder law $\mu K_{x_0}\cdots K_{x_{h-1}}\mathbf 1$ (p.2) → closed form $\sum_{n\ge0}\mu Q_h^n c$ of Appendix C, p.28; reason: the paper states both forms of the same quantity; every term is nonnegative
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Theorem B.4 (i), proof, (B.15), p.24 (PDF 26); §7, p.10 (PDF 12)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
open MeasureTheory

namespace TwoBoxMemory

/-- (B.15), rational separation. Let `r = r₁/r₂`, `s = s₁/s₂`, `β = b₁/b₂` be rationals in lowest
positive terms forming a non-tie positive saddle with irrational logarithmic failure ratio, and
`Z = max(r₂, s₂)`. Then `Z > 1`, `|β r^i − s^j| ≥ 1/(b₂ Z^{i+j})` for all `i, j ≥ 0`, and for every
`M ≥ 1`, `Δ_M ≥ (G/(2b₂)) Z^{−F_M} ≥ (G/(2b₂)) Z^{−2H_M}`.

**Formalization Note.** `r₂, s₂, b₂` are the denominators `Rat.den` of the reduced fractions;
`Z^{−n}` is written `1 / Z^n`.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Theorem B.4 (i), proof, (B.15), p.24 (PDF 26); §7, p.10 (PDF 12).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem eq_B15_rational_separation (r s β : ℚ) (D : ℝ) (hS : IsSaddle r s β D) :
    1 < max r.den s.den ∧
    (∀ i j : ℕ, 1 / ((β.den : ℝ) * ((max r.den s.den : ℕ) : ℝ) ^ (i + j)) ≤
      |(β : ℝ) * (r : ℝ) ^ i - (s : ℝ) ^ j|) ∧
    ∀ M : ℕ, 1 ≤ M →
      Gconst r s β D / (2 * β.den) * (1 / ((max r.den s.den : ℕ) : ℝ) ^ profF (greedyWord r s β) M) ≤
          gap r s (saddleCost r s β D) D M ∧
        Gconst r s β D / (2 * β.den) *
            (1 / ((max r.den s.den : ℕ) : ℝ) ^ (2 * profH (greedyWord r s β) M)) ≤
          Gconst r s β D / (2 * β.den) *
            (1 / ((max r.den s.den : ℕ) : ℝ) ^ profF (greedyWord r s β) M) := by sorry

end TwoBoxMemory
