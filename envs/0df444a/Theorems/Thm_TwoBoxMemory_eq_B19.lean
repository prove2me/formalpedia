-- Prove2me | Theorems.Thm_TwoBoxMemory_eq_B19
-- name    : TwoBoxMemory.eq_B19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:49.744397+00:00
-- url     : https://prove2.me/theorems/1f33dddc-c521-46e5-ba22-d85df268d272
-- title:
--   (B.19) — $\Delta_{29}(C^*)\le2^{-180}$ and $\Delta_{29}\le2^{-150}\Delta_{28}$
-- statement:
--   At $r=1/7$, $s=2/3$, $D=1$ and the saddle cost $C^*$, the deterministic 29-cycle controller has worst risk at most $V+2^{-180}$; consequently
--
--   $$\Delta_{29}\le2^{-180},\qquad \Delta_{29}\le2^{-150}\,\Delta_{28} .$$
--
--   One additional label reduces the optimal excess by a factor of at least $2^{150}$ at the auxiliary saddle.
--
--   Differences from the source:
--   - encoding: $\Delta_M=V_M-V$ with $V_M,V\in[0,\infty]$ → `gap` $=(V_M).\mathrm{toReal}-V.\mathrm{toReal}$; reason: both values are finite for $M\ge1$ (proved in the verification file), so the real difference is exact
--   - encoding: controller risk as the risk (B.4) of the cylinder law $\mu K_{x_0}\cdots K_{x_{h-1}}\mathbf 1$ (p.2) → closed form $\sum_{n\ge0}\mu Q_h^n c$ of Appendix C, p.28; reason: the paper states both forms of the same quantity; every term is nonnegative
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), (B.19), p.26 (PDF 28); Appendix G, p.57 (PDF 59)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
import Definitions.Def_TwoBoxMemory_Instance
open MeasureTheory

namespace TwoBoxMemory

/-- (B.19). At `r = 1/7`, `s = 2/3`, `D = 1` and the saddle cost `C*`: the deterministic 29-cycle
controller has excess at most `2^{−180}` over `V`, hence `Δ₂₉ ≤ 2^{−180}` and
`Δ₂₉ ≤ 2^{−150} Δ₂₈`.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
(B.19), p.26 (PDF 28); Appendix G, p.57 (PDF 59).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem eq_B19 :
    worstRisk (1 / 7) (2 / 3) Cstar 1 cycleController ≤
      value (1 / 7) (2 / 3) Cstar 1 + ENNReal.ofReal ((2 : ℝ) ^ (-180 : ℤ)) ∧
    gap (1 / 7) (2 / 3) Cstar 1 29 ≤ (2 : ℝ) ^ (-180 : ℤ) ∧
    gap (1 / 7) (2 / 3) Cstar 1 29 ≤ (2 : ℝ) ^ (-150 : ℤ) * gap (1 / 7) (2 / 3) Cstar 1 28 := by sorry

end TwoBoxMemory
