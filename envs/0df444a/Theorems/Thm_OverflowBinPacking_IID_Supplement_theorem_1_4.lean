-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_Supplement_theorem_1_4
-- name    : OverflowBinPacking.IID.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:54:57.191826+00:00
-- url     : https://prove2.me/theorems/85ecdfec-a827-4a30-9411-66b526996e7c
-- title:
--   Theorem 1.4 — Independent exponential sizes: logarithmic and constant guarantees
-- statement:
--   Let $C\ge1$ be the overflow penalty and let the independent nonnegative sizes have exponential laws with arbitrary positive rates $r_i$. There are absolute positive constants $K_1,K_2$ and a threshold $C_0>1$, uniform in the horizon and the rates, such that for $C\ge C_0$ and every sequential policy $a$,
--   $$\operatorname{cost}(\mathrm{BG}_{2})\le K_1\log C\operatorname{cost}(a).$$
--   If every $r_i\ge2\log C$, then additionally
--   $$\operatorname{cost}(\mathrm{BG}_{1})\le K_2\operatorname{cost}(a).$$
--   The two clauses retain the different risk parameters specified by §§5.1–5.2. No light-rate assumption is added to the first clause. The empty horizon is included. These results concern independent inputs, without an identical-distribution assumption.
--
--   Differences from the source:
--   - encoding: sequential policies and bins → the published zero-based Rule on Fin n, with measurable nonanticipative choices and strict overflow; reason: the immutable model is reused; measurability makes all expectations meaningful and changes no finite-support instance
--   - encoding: O(log C) and O(1) → positive constants and a threshold quantified before C, n, laws and rates; reason: this is the source asymptotic meaning, avoiding the invalid log C=0 bound at C=1
--   - reading: Budgeted Greedy in both clauses → gamma=2 for arbitrary rates and gamma=1 for the small-size regime; reason: Propositions 5.2 and 5.4 and their proofs specify these parameters
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 5, Theorem 1.4

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Supplement_Capacity
import Definitions.Def_OverflowBinPacking_IID_BudgetedGreedy

namespace OverflowBinPacking.IID.Supplement
open MeasureTheory

theorem theorem_1_4 :
    ∃ K₁ K₂ C₀ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ 1 < C₀ ∧
      ∀ (C : ℝ), C₀ ≤ C → ∀ (n : ℕ) (μ : Fin n → Measure ℝ)
        (rates : Fin n → ℝ), (∀ i, ExponentialLaw (μ i) (rates i)) →
          (∀ a : Rule n, IsPolicy a →
            cost μ C (bgRule μ C 2) ≤ K₁ * Real.log C * cost μ C a) ∧
          ((∀ i, 2 * Real.log C ≤ rates i) →
            ∀ a : Rule n, IsPolicy a →
              cost μ C (bgRule μ C 1) ≤ K₂ * cost μ C a) := by sorry

end OverflowBinPacking.IID.Supplement
