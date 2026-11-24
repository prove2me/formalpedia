-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_Supplement_theorem_6_1
-- name    : OverflowBinPacking.IID.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:57:34.593444+00:00
-- url     : https://prove2.me/theorems/00c338b0-60ab-4594-84f2-26995ee5af3f
-- title:
--   Theorem 6.1 (corrected: explicit small-accuracy range and clock obstruction)
-- statement:
--   In the small-accuracy regime supported by the geometric bound on p.24, let $0<\varepsilon\le r=(\sqrt{15}-3)/6$. For independent input laws supported in $[0,1+\varepsilon]$ and $C\ge1$, a uniform finite compiler computes a polynomial-size policy with
--   $$T\le K\varepsilon^{-10}n^{2/\varepsilon^5},\qquad \operatorname{cost}_{1+6\varepsilon}(\mathcal P)\le(1+4\varepsilon)\operatorname{cost}_1(a)$$
--   for every unit-capacity sequential comparator $a$. The positive constant $K$ is independent of the input, penalty and accuracy. The statement also records the obstruction to extending a uniform positive clock bound to all positive accuracies:
--   $$\neg\exists K>0\ \forall\varepsilon>0,\quad 1\le K/\varepsilon^{10}.$$
--   This corrected target retains both algorithmic and cost clauses on the repaired domain. At $n=1$ the printed runtime tends to zero as accuracy grows, so the brief's unrestricted uniform-in-accuracy reading cannot hold for any program charged at least one operation.
--
--   Differences from the source:
--   - encoding: an algorithm computing a polynomial-size sequential policy → finite rational-literal compiler and decision programs on an instruction-level real RAM, with distribution CDF and truncated-moment queries charged one operation; reason: the source evaluates atom probabilities and conditional means; actual run, halting, output, decision fuel and total charged operations are theorem conclusions, so output length alone cannot stand in for computation
--   - reading: the coupling-based policy simulations of §6 → independent uniform tapes for simulation and a deterministic feasible rule for each fixed tape, with expected cost averaged over tapes; reason: this represents the paper's causal randomized simulation; the benchmark remains every deterministic sequential policy
--   - encoding: a list of n arriving items → n at least one for the asymptotic running-time statement; reason: the empty input has zero packing cost; a positive clock bound cannot be bounded by zero to a positive power
--   - correction: Theorem 6.1 has no displayed upper accuracy bound and the brief requests a uniform operation constant on all positive accuracies → epsilon is at most (sqrt(15)-3)/6, and the statement also refutes the unrestricted uniform clock bound; reason: at n=1 every halting run costs at least one while K/epsilon^10 tends to zero; p.24 and Proposition 6.6 provide the exact repaired range; all larger epsilon values are explicitly excluded, see DISPROOF.md
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 20, Theorem 6.1

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Supplement_Computation
import Definitions.Def_OverflowBinPacking_IID_Supplement_Discretization

namespace OverflowBinPacking.IID.Supplement
open MeasureTheory

/-- Corrected small-accuracy regime used by Proposition 6.6 and its two conversions. -/
theorem theorem_6_1 :
    (¬ ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → 1 ≤ K / ε ^ 10) ∧
    ∃ A : Scheme, A.Allowed ∧ ∃ K : ℝ, 0 < K ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ trackingRange →
        ∃ b d : ℕ, 0 < b ∧ ∀ (n : ℕ), 1 ≤ n →
          ∀ (μ : Fin n → Measure ℝ), BoundedInput μ ε → ∀ C : ℝ, 1 ≤ C →
            A.Compiles μ C ε
              (K / ε ^ 10 * Real.rpow (n : ℝ) (2 / ε ^ 5))
              b d (1 + 6 * ε) (1 + 4 * ε) := by sorry

end OverflowBinPacking.IID.Supplement
