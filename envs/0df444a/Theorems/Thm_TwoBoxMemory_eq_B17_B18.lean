-- Prove2me | Theorems.Thm_TwoBoxMemory_eq_B17_B18
-- name    : TwoBoxMemory.eq_B17_B18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:53.98346+00:00
-- url     : https://prove2.me/theorems/fdbc7c0f-6af7-41c7-adc2-fa21a6c55899
-- title:
--   (B.17)–(B.18) — the gap $g^*$ and $\Delta_{28}(C^*)\ge g^*/3\ge2^{-30}$
-- statement:
--   At $r=1/7$, $s=2/3$, $\beta=5/4$, the smallest index gap over $i+j\le56$ is
--
--   $$\min_{i+j\le56}|\beta r^i-s^j|=g^*=\frac{35195023535349249073699}{10014242608881728162181268645284},$$
--
--   attained at $(i,j)=(10,46)$; and at the saddle cost $C^*$ with $D=1$,
--
--   $$\Delta_{28}\ \ge\ g^*/3\ \ge\ 2^{-30} .$$
--
--   Every real randomized 28-label controller is covered by this lower bound.
--
--   Differences from the source:
--   - encoding: $\Delta_M=V_M-V$ with $V_M,V\in[0,\infty]$ → `gap` $=(V_M).\mathrm{toReal}-V.\mathrm{toReal}$; reason: both values are finite for $M\ge1$ (proved in the verification file), so the real difference is exact
--   - encoding: controller risk as the risk (B.4) of the cylinder law $\mu K_{x_0}\cdots K_{x_{h-1}}\mathbf 1$ (p.2) → closed form $\sum_{n\ge0}\mu Q_h^n c$ of Appendix C, p.28; reason: the paper states both forms of the same quantity; every term is nonnegative
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), (B.17)–(B.18), p.26 (PDF 28); Appendix G, p.57 (PDF 59)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
import Definitions.Def_TwoBoxMemory_Instance
open MeasureTheory

namespace TwoBoxMemory

/-- (B.17)–(B.18). At `r = 1/7`, `s = 2/3`, `β = 5/4`: the minimum of `|β r^i − s^j|` over
`i + j ≤ 56` is `g* = 35195023535349249073699 / 10014242608881728162181268645284`, attained at
`(i, j) = (10, 46)`, and at the saddle cost `C*` (with `D = 1`), `Δ₂₈ ≥ g*/3 ≥ 2^{−30}`.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
(B.17)–(B.18), p.26 (PDF 28); Appendix G, p.57 (PDF 59).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem eq_B17_B18 :
    minIndexGap (1 / 7) (2 / 3) (5 / 4) 56 = gstar ∧
    |(5 / 4 : ℝ) * (1 / 7) ^ 10 - (2 / 3) ^ 46| = gstar ∧
    gstar / 3 ≤ gap (1 / 7) (2 / 3) Cstar 1 28 ∧ (2 : ℝ) ^ (-30 : ℤ) ≤ gstar / 3 := by sorry

end TwoBoxMemory
