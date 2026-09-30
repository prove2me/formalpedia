-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_canonical_capped_chart_cost
-- name    : WeierstrassEllipticZeta.canonical_capped_chart_cost
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-21T13:49:49.904751+00:00
-- url     : https://prove2.me/theorems/cd728a22-beab-4ad0-9c0b-5262083d2fdf
-- title:
--   Finite canonical chart costs and optimal positive budgets
-- statement:
--   For any capped chart data, the set of relevant persistent-component length values at a fixed chart point is finite. Its maximum with 1, denoted E(c,z), is positive. Whenever z belongs to the specified finite set and the chart denominator is nonzero, E(c,z) gives a valid capped chart budget at that same chart and point.
--
--   It is the least positive such budget: for every positive e and every budget B, E(B.chart,B.z) <= e.
--
--   Consequently, if a nonempty family of k labels has positive weights e_i and valid capped budgets, there is one valid chart point (c,z) for which k*E(c,z) <= sum_i e_i. Thus the whole family can be replaced by a constant family using one canonical local cost, without increasing the total.
--
--   The theorem gives existence, finiteness, optimality and a comparison of total costs. It does not bound E(c,z) in terms of the original polynomial bidegree or prove A.1's uniform geometric estimate.
-- source:
--   Canonical positive local costs for the current A.1 capped-budget interface. Noetherian minimal-prime finiteness is Stacks Project Lemma 10.31.6, https://stacks.math.columbia.edu/tag/00FR. Finite length of the quotient localized at a minimal prime follows from the local-support criterion, Lemma 10.62.3, https://stacks.math.columbia.edu/tag/00L5; the Lean proof uses the equivalent zero-dimensional Noetherian-to-Artinian criterion. E(c,z) is the maximum of 1 and the finite set of lengths tested by the budget. It is the least positive budget at that chart point. For k nonempty labels, minimizing the old weights gives k*E(c,z) <= sum_i e_i, since the budget predicate is label-independent. This finite-maximum construction is derived for the mission's interface, not quoted from Kumar's Appendix A. The equivalent frontier retains W and C. No algorithm for computing components, bidegree estimate, or proof of the remaining uniform k*E bound is asserted.

import Definitions.Def_WeierstrassEllipticZeta_CanonicalChartCost
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Tactic

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.canonical_capped_chart_cost
    (L : PeriodPair) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (N T : ℕ) (Z : Finset ℂ) :
    (∀ (c : Fin 2) (z : ℂ),
      (cappedChartLengthValues L S Q N T c z).Finite ∧
      0 < cappedChartCost L S Q N T c z ∧
      (z ∈ Z → S (extensionChartDenominator c) z ≠ 0 →
        ∃ B : CappedChartJetBudget L S Q N T (cappedChartCost L S Q N T c z) Z,
          B.chart = c ∧ B.z = z)) ∧
    (∀ (e : ℕ), 0 < e → ∀ B : CappedChartJetBudget L S Q N T e Z,
      cappedChartCost L S Q N T B.chart B.z ≤ e) ∧
    (∀ (ι : Type) [Fintype ι] [Nonempty ι] (e : ι → ℕ),
      (∀ i, 0 < e i) → (∀ i, Nonempty (CappedChartJetBudget L S Q N T (e i) Z)) →
      ∃ (c : Fin 2) (z : ℂ), z ∈ Z ∧ S (extensionChartDenominator c) z ≠ 0 ∧
        Fintype.card ι * cappedChartCost L S Q N T c z ≤ ∑ i, e i) := by sorry
