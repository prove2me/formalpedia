-- Prove2me | Theorems.Thm_TwoBoxMemory_theorem_B_4_ae_separation
-- name    : TwoBoxMemory.theorem_B_4_ae_separation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:43.433548+00:00
-- url     : https://prove2.me/theorems/c0153657-4e45-44e8-bf43-f2b9d6c48607
-- title:
--   Theorem B.4 (ii) — almost every index $\beta$ is exponentially separated
-- statement:
--   Fix failure probabilities $r,s\in(0,1)$ with $\log r/\log s$ irrational. Then for Lebesgue-almost every $\beta>0$ there are constants $a,c>0$ with
--
--   $$|\beta r^i-s^j|\ \ge\ a\,e^{-c(i+j)}\qquad\text{for all integers } i,j\ge0 .$$
--
--   This is case (ii) of Theorem B.4: generic indices satisfy the separation hypothesis of the two-sided bound (B.14).
--
--   Differences from the source:
--   - generalization: for Lebesgue almost every index β satisfying u, v > 0 → for Lebesgue almost every β > 0; reason: the proof works on the whole positive axis (p.24); restricting to the β with u, v > 0 gives the source's claim
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Theorem B.4 (ii) and its proof, p.24 (PDF 26); §7, p.10 (PDF 12)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
open MeasureTheory

namespace TwoBoxMemory

/-- Theorem B.4 (ii), almost-every separation. For fixed `r, s ∈ (0, 1)` with `log r / log s`
irrational, Lebesgue-almost every index `β > 0` has exponential separation (B.13): there are
`a, c > 0` with `|β r^i − s^j| ≥ a e^{−c(i+j)}` for all `i, j ≥ 0`.

**Formalization Note.** The statement is over all `β > 0`; the paper restricts afterwards to the
`β` with `u, v > 0`.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Theorem B.4 (ii) and its proof, p.24 (PDF 26); §7, p.10 (PDF 12).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem theorem_B_4_ae_separation (r s : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s)
    (hs1 : s < 1) (hirr : Irrational (Real.log r / Real.log s)) :
    ∀ᵐ β ∂(volume : Measure ℝ), 0 < β → Sep r s β := by sorry

end TwoBoxMemory
