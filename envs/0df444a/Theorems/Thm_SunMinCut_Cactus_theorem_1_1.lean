-- Prove2me | Theorems.Thm_SunMinCut_Cactus_theorem_1_1
-- name    : SunMinCut.Cactus.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:25:19.301725+00:00
-- url     : https://prove2.me/theorems/ee460980-7120-40bb-a6f5-a1fe9ad265c9
-- title:
--   Theorem 1.1 — a minimum cut and the cactus of all minimum cuts in O_ζ(m log n) operations
-- statement:
--   For every fixed $\zeta>0$ there are one randomized program for the unit-cost real RAM of footnote 1 (arithmetic, comparisons, powers, logarithms, rounding, uniform draws from $[0,1]$), fixed before the input, and one constant $C$ depending on $\zeta$ only, such that for every connected graph $G$ with $n\ge2$ vertices, $m$ stored edge records and positive real capacities (the minimum-cut value is not supplied):
--   1. every execution halts within $C\,m\log n$ operations (natural logarithm);
--   2. with probability at least $1-n^{-\zeta}$ (product uniform measure on the draws) the output is a minimum cut $S$ together with a cactus $(K,\pi)$ representing exactly all minimum cuts of $G$.
--
--   Differences from the source:
--   - encoding: "in O(·) operations the procedure …" (a statement about the paper's procedure) → there exist one admissible program P for the real RAM of footnote 1 and one constant C, chosen before every input, with the stated time bound on every draw tape; reason: the O(·) is unpacked with its constant fixed before the input, and the procedure is the program that realizes it
--   - generalization: a program for the unit-cost real RAM (machine constants unrestricted) → the program must be admissible: rational constants only; reason: a stronger claim; an admissible program is in particular a real-RAM program, so the Lean statement implies the source's
--   - encoding: "with probability at least p" → the (outer) product-uniform measure of the failure set of draw tapes is at most 1 − p; reason: implies the probability statement for the measurable success event and needs no measurability side condition
--   - encoding: the arithmetic, logarithm and power operations of footnote 1 → division by zero is zero, log uses log(abs x), and power returns zero on negative bases instead of using the cosine continuation of Real.rpow; reason: explicit totalization at exceptional inputs using constant-cost guards; the paper’s uses of real powers have nonnegative bases and no trigonometric operation is introduced
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Theorem 1.1, p. 2

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph
import Definitions.Def_SunMinCut_Cactus_CactusGraph
import Definitions.Def_SunMinCut_Cactus_Machine

open MeasureTheory

namespace SunMinCut.Cactus

/-- **Theorem 1.1 (Minimum cuts and their cactus)**, Sun 2026, doi:10.5281/zenodo.23915020, p. 2:
for every fixed `ζ > 0` there are one randomized program for the unit-cost real RAM with uniform
draws and one constant `C` (depending on `ζ` only) such that, on every connected graph with
`n ≥ 2` vertices, `m` edge records and positive real capacities (the minimum-cut value is not
supplied), every execution halts within `C m log n` operations, and with probability at least
`1 − n^{−ζ}` the output is a minimum cut together with a cactus representing exactly all minimum
cuts. -/
theorem theorem_1_1 :
    ∀ ζ : ℝ, 0 < ζ → ∃ P : Program, Admissible P ∧ ∃ C : ℝ,
      ∀ (n m : ℕ), 2 ≤ n → ∀ G : Graph n m, Positive G → Connected G →
      ∀ l : List ℝ, GraphCode G l →
        HaltsWithin P l (C * m * Real.log n) ∧
        tapeMeasure {ω | ¬ ∃ (S : Finset (Fin n)) (q e : ℕ) (K : MGraph q e) (π : Fin n → Fin q),
          CutCactusOut S K π (outputAt P l (C * m * Real.log n) ω) ∧
          IsMinCut G S ∧ RepresentsMinCuts G K π} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-ζ)) := by sorry

end SunMinCut.Cactus
