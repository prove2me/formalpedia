-- Prove2me | Theorems.Thm_SunMinCut_Cactus_lemma_2_3
-- name    : SunMinCut.Cactus.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:25:33.353183+00:00
-- url     : https://prove2.me/theorems/189dec52-a65e-4a84-95c0-5df1c16e56c1
-- title:
--   Lemma 2.3 — an actual cut of capacity below 9λ/4 in O((s + n) log(8n)) work
-- statement:
--   There are one admissible deterministic program and one constant $C$ such that, for every connected graph $G$ on $n\ge2$ vertices with positive capacities, aggregated into $m=s$ distinct endpoint pairs, and every encoding of it as input, every execution halts within $C(s+n)\log(8n)$ operations (natural logarithm) and outputs a single real $c_0$ that is the capacity of an actual cut (some shore $S$ has $w(\delta S)=c_0$) and satisfies $\lambda\le c_0<9\lambda/4$.
--
--   Differences from the source:
--   - encoding: "in O(·) operations the procedure …" (a statement about the paper's procedure) → there exist one admissible program P for the real RAM of footnote 1 and one constant C, chosen before every input, with the stated time bound on every draw tape; reason: the O(·) is unpacked with its constant fixed before the input, and the procedure is the program that realizes it
--   - generalization: a program for the unit-cost real RAM (machine constants unrestricted) → the program must be admissible: rational constants only; reason: a stronger claim; an admissible program is in particular a real-RAM program, so the Lean statement implies the source's
--   - encoding: input with s aggregated endpoint pairs and bound in s → Aggregated G (no loops, no repeated pair), so m = s, and the bound written with m; reason: the procedure takes the aggregated graph of §2 as input
--   - encoding: deterministic work (Appendix B.1 or Appendix G) → Deterministic P forbids uniform-draw instructions, with the guarantee on every tape; reason: the run is independent of the tape; this states determinism directly
--   - encoding: the arithmetic, logarithm and power operations of footnote 1 → division by zero is zero, log uses log(abs x), and power returns zero on negative bases instead of using the cosine continuation of Real.rpow; reason: explicit totalization at exceptional inputs using constant-cost guards; the paper’s uses of real powers have nonnegative bases and no trigonometric operation is introduced
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Lemma 2.3, p. 8

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph
import Definitions.Def_SunMinCut_Cactus_Machine

namespace SunMinCut.Cactus

/-- **Lemma 2.3**, Sun 2026, doi:10.5281/zenodo.23915020, p. 8: there are one program and one
constant `C` such that, on every aggregated connected graph with positive capacities
(`m = s` records), every execution halts within `C (s + n) log(8n)` operations and outputs the
capacity `c₀` of an actual cut with `λ ≤ c₀ < 9λ/4`. -/
theorem lemma_2_3 :
    ∃ P : Program, Admissible P ∧ Deterministic P ∧ ∃ C : ℝ,
      ∀ (n m : ℕ), 2 ≤ n → ∀ G : Graph n m, Positive G → Connected G → Aggregated G →
      ∀ l : List ℝ, GraphCode G l →
        HaltsWithin P l (C * ((m : ℝ) + n) * Real.log (8 * n)) ∧
        ∀ ω : Tape, ∃ c0 : ℝ, outputAt P l (C * ((m : ℝ) + n) * Real.log (8 * n)) ω = [c0] ∧
          CoarseCut G c0 := by sorry

end SunMinCut.Cactus
