-- Prove2me | Theorems.Thm_SunMinCut_Cactus_theorem_2_1
-- name    : SunMinCut.Cactus.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:24:58.822199+00:00
-- url     : https://prove2.me/theorems/d6e44066-1008-4079-83e2-06bc5992124d
-- title:
--   Theorem 2.1 — O_ζ(m + (s + n) log(2n)) time, O(n)-size cactus, always an actual cut
-- statement:
--   For every fixed $\zeta>0$ there are one admissible program and one constant $C$ (depending on $\zeta$ only) such that, for every connected graph $G$ with $n\ge2$ vertices, $m$ records, $s$ distinct endpoint pairs and positive real capacities, given only $G$ (the minimum-cut value is not supplied):
--   1. every execution halts within $C\,(m+(s+n)\log(2n))$ operations and returns an actual nontrivial cut;
--   2. with probability at least $1-n^{-\zeta}$ the returned cut is a minimum cut and the output also contains a cactus $(K,\pi)$ with at most $Cn$ nodes and edges representing exactly all minimum cuts.
--
--   Differences from the source:
--   - encoding: "in O(·) operations the procedure …" (a statement about the paper's procedure) → there exist one admissible program P for the real RAM of footnote 1 and one constant C, chosen before every input, with the stated time bound on every draw tape; reason: the O(·) is unpacked with its constant fixed before the input, and the procedure is the program that realizes it
--   - generalization: a program for the unit-cost real RAM (machine constants unrestricted) → the program must be admissible: rational constants only; reason: a stronger claim; an admissible program is in particular a real-RAM program, so the Lean statement implies the source's
--   - encoding: "with probability at least p" → the (outer) product-uniform measure of the failure set of draw tapes is at most 1 − p; reason: implies the probability statement for the measurable success event and needs no measurability side condition
--   - encoding: O(n)-size cactus → q + e ≤ C·n with the same constant C, inside the success event; reason: the size claim belongs to the cactus the theorem constructs with high probability
--   - encoding: the arithmetic, logarithm and power operations of footnote 1 → division by zero is zero, log uses log(abs x), and power returns zero on negative bases instead of using the cosine continuation of Real.rpow; reason: explicit totalization at exceptional inputs using constant-cost guards; the paper’s uses of real powers have nonnegative bases and no trigonometric operation is introduced
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Theorem 2.1, p. 7

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph
import Definitions.Def_SunMinCut_Cactus_CactusGraph
import Definitions.Def_SunMinCut_Cactus_Machine

open MeasureTheory

namespace SunMinCut.Cactus

/-- **Theorem 2.1**, Sun 2026, doi:10.5281/zenodo.23915020, p. 7: for every fixed `ζ > 0` there
are one randomized program and one constant `C` (depending on `ζ` only) such that, on every
connected graph with `n ≥ 2` vertices, `m` records (`s` distinct endpoint pairs) and positive real
capacities (`λ` not supplied): every execution halts within `C (m + (s + n) log(2n))` operations
and returns an actual nontrivial cut; and with probability at least `1 − n^{−ζ}` the cut is a
minimum cut and the output also contains a cactus with at most `C n` nodes and edges representing
exactly all minimum cuts. -/
theorem theorem_2_1 :
    ∀ ζ : ℝ, 0 < ζ → ∃ P : Program, Admissible P ∧ ∃ C : ℝ,
      ∀ (n m : ℕ), 2 ≤ n → ∀ G : Graph n m, Positive G → Connected G →
      ∀ l : List ℝ, GraphCode G l →
        HaltsWithin P l (C * ((m : ℝ) + ((supportCount G : ℝ) + n) * Real.log (2 * n))) ∧
        (∀ ω : Tape, ∃ (S : Finset (Fin n)) (rest : List ℝ),
          outputAt P l (C * ((m : ℝ) + ((supportCount G : ℝ) + n) * Real.log (2 * n))) ω =
            shoreList S ++ rest ∧ Nontriv S) ∧
        tapeMeasure {ω | ¬ ∃ (S : Finset (Fin n)) (q e : ℕ) (K : MGraph q e) (π : Fin n → Fin q),
          CutCactusOut S K π
            (outputAt P l (C * ((m : ℝ) + ((supportCount G : ℝ) + n) * Real.log (2 * n))) ω) ∧
          IsMinCut G S ∧ RepresentsMinCuts G K π ∧ (q : ℝ) + e ≤ C * n} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-ζ)) := by sorry

end SunMinCut.Cactus
