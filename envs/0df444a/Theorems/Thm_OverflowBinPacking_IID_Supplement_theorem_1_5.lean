-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_Supplement_theorem_1_5
-- name    : OverflowBinPacking.IID.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:55:52.404931+00:00
-- url     : https://prove2.me/theorems/d1991f6e-b9e4-4725-89c1-6d49819b8c49
-- title:
--   Theorem 1.5 — Full soft-capacity PTAS with polynomial finite policy representation
-- statement:
--   For every $0<\varepsilon\le\sqrt6(\sqrt{15}-3)$, an admissible uniform compiler and decision program, given independent nonnegative input laws and $C\ge1$, produces a finite policy at capacity $1+\varepsilon$. For each fixed accuracy its representation and placement fuel are polynomial in $n$. A uniform constant $K>0$ bounds charged operations by
--   $$K\varepsilon^{-10}n^{2(6/\varepsilon)^5}.$$
--   For every unit-capacity sequential policy $a$ the output's expected cost satisfies
--   $$\operatorname{cost}_{1+\varepsilon}(\mathcal P)\le(1+\varepsilon)\operatorname{cost}_1(a).$$
--   The full printed accuracy interval is retained, including values beyond the small-parameter proof on p.24. Resolving that proof gap is part of proving this target. No accuracy range or distribution support restriction is added. The executable representation and resource obligations are part of the conclusion, not an assumed optimal-policy oracle.
--
--   Differences from the source:
--   - encoding: an algorithm computing a polynomial-size sequential policy → finite rational-literal compiler and decision programs on an instruction-level real RAM, with distribution CDF and truncated-moment queries charged one operation; reason: the source evaluates atom probabilities and conditional means; actual run, halting, output, decision fuel and total charged operations are theorem conclusions, so output length alone cannot stand in for computation
--   - reading: the coupling-based policy simulations of §6 → independent uniform tapes for simulation and a deterministic feasible rule for each fixed tape, with expected cost averaged over tapes; reason: this represents the paper's causal randomized simulation; the benchmark remains every deterministic sequential policy
--   - encoding: a list of n arriving items → n at least one for the asymptotic running-time statement; reason: the empty input has zero packing cost; a positive clock bound cannot be bounded by zero to a positive power
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 6, Theorem 1.5

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Supplement_Computation

namespace OverflowBinPacking.IID.Supplement
open MeasureTheory

theorem theorem_1_5 :
    ∃ A : Scheme, A.Allowed ∧ ∃ K : ℝ, 0 < K ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt 6 * (Real.sqrt 15 - 3) →
        ∃ b d : ℕ, 0 < b ∧ ∀ (n : ℕ), 1 ≤ n →
          ∀ (μ : Fin n → Measure ℝ), InputLaws μ → ∀ C : ℝ, 1 ≤ C →
            A.Compiles μ C ε
              (K / ε ^ 10 * Real.rpow (n : ℝ) (2 * (6 / ε) ^ 5))
              b d (1 + ε) (1 + ε) := by sorry

end OverflowBinPacking.IID.Supplement
