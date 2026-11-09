-- Prove2me | Theorems.Thm_TriFreeEst247_Main_estimation_le_poly_testing
-- name    : TriFreeEst247.Main.estimation_le_poly_testing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:02:02.326216+00:00
-- url     : https://prove2.me/theorems/b4c2edc1-6115-4e08-8af9-82f1dea08e5e
-- title:
--   Theorem 1.1: estimation is polynomial in testing at ε/8
-- statement:
--   There are absolute constants $C>0$ and $d\in\mathbb N$ such that for every $0<\varepsilon<1$,
--
--   $$E_\triangle(\varepsilon)\le C T_\triangle(\varepsilon/8)^d.$$
--
--   Here $T_\triangle$ is the minimum worst-case number of adjacency queries of a two-sided triangle-freeness tester with success probability at least $2/3$, and $E_\triangle$ is the analogous minimum for an additive estimator of the distance normalized by $n^2$. Both minima require one query bound for all graph orders $n\ge1$.
--
--   This is the paper's full testing-to-estimation comparison. Constants are independent of the accuracy and the graph; algorithms receive only the order and oracle access. The triangle removal lemma supplies finite testing bounds, so infinity does not trivialize the conclusion on the stated domain.
--
--   Differences from the source:
--   - reading: poly(T△(ε/8)) → C T△(ε/8)ᵈ, with C>0 and d natural before ε; reason: the polynomial and O constants are absolute and quantified before every varying parameter
--   - encoding: minimum worst-case randomized query complexities → ENat minima embedded in ENNReal with PMF decision-tree algorithms; reason: depth pruning and the finite partition by success-interval endpoints preserve all source success probabilities, as detailed in MODERATION_NOTES
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.3, Theorem 1.1

import Mathlib
import Definitions.Def_TriFreeEst247_Main_GraphModel

open scoped ENNReal

namespace TriFreeEst247.Main

theorem estimation_le_poly_testing :
    ∃ C : ℝ, ∃ d : ℕ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (estimationComplexity ε).toENNReal ≤
        ENNReal.ofReal C * (testingComplexity (ε / 8)).toENNReal^d := by sorry

end TriFreeEst247.Main
