-- Prove2me | Theorems.Thm_TwoBoxMemory_theorem_B_4_bounds
-- name    : TwoBoxMemory.theorem_B_4_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:44.327145+00:00
-- url     : https://prove2.me/theorems/1bfd62d2-9d43-4219-8e49-63ca557204cd
-- title:
--   Theorem B.4, display (B.14) — two-sided bound under exponential separation
-- statement:
--   Throughout, $(r,s,\beta,D)$ is a **non-tie positive saddle with irrational logarithmic failure ratio**: $r,s\in(0,1)$ are the failure probabilities at locations $A$ and $B$ ($p=1-r$, $t=1-s$), $\log r/\log s$ is irrational, $\beta>0$, $\beta r^i\neq s^j$ for all $i,j\ge0$, $u=1/p-H_B>0$, $v=1/t-H_A>0$ and $D>0$; the cost of command $A$ is the saddle cost $C=Dv/u$, and $W$ is the greedy word. Assume exponential separation (B.13): $|\beta r^i-s^j|\ge a\,e^{-c(i+j)}$ for all $i,j\ge0$, with $a,c>0$. Then for all $M\ge2$,
--
--   $$\frac{Ga}{2}\,e^{-2cH_M}\ \le\ \Delta_M\ \le\ KM\tau^{H_M} .$$
--
--   This item is the display (B.14) of Theorem B.4; the asymptotic consequence $-\log\Delta_M=\Theta(H_M)$ is clause (b) of the goal `TwoBoxMemory.theorem_2_2`, case (i) is `TwoBoxMemory.eq_B15_rational_separation` and case (ii) is `TwoBoxMemory.theorem_B_4_ae_separation`.
--
--   Differences from the source:
--   - encoding: $\Delta_M=V_M-V$ with $V_M,V\in[0,\infty]$ → `gap` $=(V_M).\mathrm{toReal}-V.\mathrm{toReal}$; reason: both values are finite for $M\ge1$ (proved in the verification file), so the real difference is exact
--   - encoding: controller risk as the risk (B.4) of the cylinder law $\mu K_{x_0}\cdots K_{x_{h-1}}\mathbf 1$ (p.2) → closed form $\sum_{n\ge0}\mu Q_h^n c$ of Appendix C, p.28; reason: the paper states both forms of the same quantity; every term is nonnegative
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Theorem B.4, display (B.14), p.24 (PDF 26); §7, p.10 (PDF 12)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
open MeasureTheory

namespace TwoBoxMemory

/-- Theorem B.4, display (B.14) (The non-tie memory frontier). At a non-tie positive saddle with
exponential separation (B.13), `|β r^i − s^j| ≥ a e^{−c(i+j)}` for all `i, j ≥ 0` with
`a, c > 0`, for all `M ≥ 2`: `(G a / 2) e^{−2c H_M} ≤ Δ_M ≤ K M τ^{H_M}`.

This item is the display (B.14) of Theorem B.4. The theorem's asymptotic consequence
`−log Δ_M = Θ(H_M)` is clause (b) of the goal `TwoBoxMemory.theorem_2_2`, its case (i) is the item
`TwoBoxMemory.eq_B15_rational_separation` and its case (ii) is the item
`TwoBoxMemory.theorem_B_4_ae_separation`.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Theorem B.4, display (B.14), p.24 (PDF 26); §7, p.10 (PDF 12).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem theorem_B_4_bounds (r s β D : ℝ) (hS : IsSaddle r s β D) (a c : ℝ) (ha : 0 < a)
    (hc : 0 < c) (hsep : ∀ i j : ℕ, a * Real.exp (-(c * ((i : ℝ) + j))) ≤ |β * r ^ i - s ^ j|)
    (M : ℕ) (hM : 2 ≤ M) :
    Gconst r s β D * a / 2 * Real.exp (-(2 * c * profH (greedyWord r s β) M)) ≤ gap r s (saddleCost r s β D) D M ∧
    gap r s (saddleCost r s β D) D M ≤ K0' r s β (saddleCost r s β D) D * M * tau r s ^ profH (greedyWord r s β) M := by sorry

end TwoBoxMemory
