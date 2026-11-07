-- Prove2me | Theorems.Thm_TwoBoxMemory_eq_B21_cost_enclosure
-- name    : TwoBoxMemory.eq_B21_cost_enclosure
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:58.694255+00:00
-- url     : https://prove2.me/theorems/b938d6d0-852d-4d83-bd55-280112e04d4e
-- title:
--   §B.9, (B.21) — $V^*\le480$ and $|C_0/C^*-1|\le2^{-190}$
-- statement:
--   At $r=1/7$, $s=2/3$, $D=1$ and the saddle cost $C^*$, the alternating word $(AB)^\infty$ has risks
--
--   $$J_A=\frac{C^*+r}{p},\qquad J_B=\frac{C^*+1}{t},$$
--
--   so $V^*\le480$; and the dyadic cost $C_0=254613987398388214970098320848945712466442749572012796843191368/2^{200}$ satisfies
--
--   $$\Bigl|\frac{C_0}{C^*}-1\Bigr|\le2^{-190} .$$
--
--   These are the two numerical inputs of the transfer to the rational cost.
--
--   Differences from the source:
--   - encoding: commands A, B; risks in [0, ∞] → commands `Fin 2` with 0 = A, 1 = B; risks in `ℝ≥0∞`; reason: Lean convention; same instances
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), §B.9, after (B.20), and (B.21), p.27 (PDF 29); §8, p.11 (PDF 13)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
import Definitions.Def_TwoBoxMemory_Instance
open MeasureTheory

namespace TwoBoxMemory

/-- §B.9 and (B.21). At `r = 1/7`, `s = 2/3`, `D = 1` and the saddle cost `C*`: the alternating word
`(AB)^∞` has risks `(C* + r)/p` and `(C* + 1)/t`, so `V* ≤ 480`; and the dyadic cost
`C₀ = 254613987398388214970098320848945712466442749572012796843191368 / 2^{200}` satisfies
`|C₀/C* − 1| ≤ 2^{−190}`.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
§B.9, after (B.20), and (B.21), p.27 (PDF 29); §8, p.11 (PDF 13).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem eq_B21_cost_enclosure :
    wordRisk (1 / 7) (2 / 3) Cstar 1 0 (fun h => if h % 2 = 0 then 0 else 1) =
      ENNReal.ofReal ((Cstar + 1 / 7) / (1 - 1 / 7)) ∧
    wordRisk (1 / 7) (2 / 3) Cstar 1 1 (fun h => if h % 2 = 0 then 0 else 1) =
      ENNReal.ofReal ((Cstar + 1) / (1 - 2 / 3)) ∧
    value (1 / 7) (2 / 3) Cstar 1 ≤ 480 ∧ |C0 / Cstar - 1| ≤ (2 : ℝ) ^ (-190 : ℤ) := by sorry

end TwoBoxMemory
