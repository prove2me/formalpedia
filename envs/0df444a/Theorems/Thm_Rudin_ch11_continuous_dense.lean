-- Prove2me | Theorems.Thm_Rudin_ch11_continuous_dense
-- name    : Rudin.ch11_continuous_dense
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:42:03.075687+00:00
-- url     : https://prove2.me/theorems/2e12b228-d5fe-4181-abbc-374fdc139259
-- title:
--   Theorem 11.38 — continuous functions are dense in $\mathscr{L}^2[a,b]$
-- statement:
--   If $f \in \mathscr{L}^2$ on $[a, b]$ and $\varepsilon > 0$, there is a continuous function $g$ with $\|f - g\|_2 < \varepsilon$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, p. 326, Theorem 11.38

import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 11.38: the continuous functions are dense in `ℒ²` on `[a, b]`: for
`f ∈ ℒ²` on `[a, b]` and `ε > 0` there is a continuous `g` with `‖f - g‖₂ < ε`. -/
theorem ch11_continuous_dense (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : MemL2 (volume.restrict (Set.Icc a b)) f) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, Continuous g ∧
      L2Norm (volume.restrict (Set.Icc a b)) (fun x => f x - g x) < ε := by sorry

end Rudin
