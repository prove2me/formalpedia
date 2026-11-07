-- Prove2me | Theorems.Thm_TwoBoxMemory_eq_B16_auxiliary_saddle
-- name    : TwoBoxMemory.eq_B16_auxiliary_saddle
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:44.685256+00:00
-- url     : https://prove2.me/theorems/5a675a03-5ccb-4d2c-87c9-cc4b62b7ff27
-- title:
--   (B.16) — $(1/7,2/3,5/4,1)$ is a saddle with $158<C^*<159$ and $G>2/3$
-- statement:
--   Take $r=1/7$, $s=2/3$, $\beta=5/4$ and $D=1$. Then $(r,s,\beta,D)$ is a non-tie positive saddle with irrational logarithmic failure ratio: no tie $\beta r^i=s^j$ occurs, $\log(1/7)/\log(2/3)$ is irrational, and $u,v>0$. Its saddle cost satisfies
--
--   $$158<C^*=v/u<159,\qquad G=\frac{24C^*}{35C^*+72}>\frac23 .$$
--
--   This is the auxiliary instance from which the finite jump is derived.
--
--   Differences from the source: none.
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), (B.16), p.26 (PDF 28); §8, p.11 (PDF 13)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
import Definitions.Def_TwoBoxMemory_Instance
open MeasureTheory

namespace TwoBoxMemory

/-- (B.16), the auxiliary saddle. `r = 1/7`, `s = 2/3`, `β = 5/4`, `D = 1` is a non-tie positive
saddle with irrational logarithmic failure ratio (no tie, `log 7 / log(3/2)` irrational, `u, v > 0`),
its saddle cost satisfies `158 < C* = v/u < 159`, and `G = 24 C*/(35 C* + 72) > 2/3`.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
(B.16), p.26 (PDF 28); §8, p.11 (PDF 13).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem eq_B16_auxiliary_saddle :
    IsSaddle (1 / 7) (2 / 3) (5 / 4) 1 ∧ 158 < Cstar ∧ Cstar < 159 ∧
    Gconst (1 / 7) (2 / 3) (5 / 4) 1 = 24 * Cstar / (35 * Cstar + 72) ∧
    2 / 3 < Gconst (1 / 7) (2 / 3) (5 / 4) 1 := by sorry

end TwoBoxMemory
