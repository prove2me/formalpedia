-- Prove2me | Theorems.Thm_TwoBoxMemory_theorem_B_2
-- name    : TwoBoxMemory.theorem_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:59.086955+00:00
-- url     : https://prove2.me/theorems/2c8e65aa-3a75-4470-807b-6fcab28fd06c
-- title:
--   Theorem B.2 — same-budget predictive obstruction $\Delta_M\ge\tfrac12 d_{F_M}$
-- statement:
--   Throughout, $(r,s,\beta,D)$ is a **non-tie positive saddle with irrational logarithmic failure ratio**: $r,s\in(0,1)$ are the failure probabilities at locations $A$ and $B$ ($p=1-r$, $t=1-s$), $\log r/\log s$ is irrational, $\beta>0$, $\beta r^i\neq s^j$ for all $i,j\ge0$, $u=1/p-H_B>0$, $v=1/t-H_A>0$ and $D>0$; the cost of command $A$ is the saddle cost $C=Dv/u$, and $W$ is the greedy word. For every integer $M\ge1$,
--
--   $$\Delta_M\ \ge\ \tfrac12\,d_{F_M}\ \ge\ \tfrac12\,d_{2H_M}\ >\ 0,$$
--
--   where $\Delta_M=V_M-V$ and $V_M$ is the infimum of the worst risk over all real stochastic controllers with at most $M$ labels and arbitrary initial distributions.
--
--   This is the lower half of the arithmetic memory bound.
--
--   Differences from the source:
--   - encoding: $\Delta_M=V_M-V$ with $V_M,V\in[0,\infty]$ → `gap` $=(V_M).\mathrm{toReal}-V.\mathrm{toReal}$; reason: both values are finite for $M\ge1$ (proved in the verification file), so the real difference is exact
--   - encoding: controller risk as the risk (B.4) of the cylinder law $\mu K_{x_0}\cdots K_{x_{h-1}}\mathbf 1$ (p.2) → closed form $\sum_{n\ge0}\mu Q_h^n c$ of Appendix C, p.28; reason: the paper states both forms of the same quantity; every term is nonnegative
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Theorem B.2, (B.9), p.23 (PDF 25); Lemma 6.1, p.9 (PDF 11)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
open MeasureTheory

namespace TwoBoxMemory

/-- Theorem B.2 (Same-budget predictive obstruction). At a non-tie positive saddle, for every
integer `M ≥ 1`, `Δ_M ≥ ½ d_{F_M} ≥ ½ d_{2H_M} > 0` (B.9). The infimum `V_M` ranges over all
real stochastic controllers with at most `M` labels and arbitrary initial rows.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Theorem B.2, (B.9), p.23 (PDF 25); Lemma 6.1, p.9 (PDF 11).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem theorem_B_2 (r s β D : ℝ) (hS : IsSaddle r s β D) (M : ℕ) (hM : 1 ≤ M) :
    departureMargin r s β D (profF (greedyWord r s β) M) / 2 ≤ gap r s (saddleCost r s β D) D M ∧
    departureMargin r s β D (2 * profH (greedyWord r s β) M) / 2 ≤
      departureMargin r s β D (profF (greedyWord r s β) M) / 2 ∧
    0 < departureMargin r s β D (2 * profH (greedyWord r s β) M) / 2 := by sorry

end TwoBoxMemory
