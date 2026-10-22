-- Prove2me | Theorems.Thm_PartialLostSales_ACOI_lemma_3
-- name    : PartialLostSales.ACOI.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:42.311597+00:00
-- url     : https://prove2.me/theorems/118a7df1-e232-4ff6-be32-9102bfe43d89
-- title:
--   Lemma 3, p. 12 — Assumption B(i): the optimal average cost w* = inf_z w(z) of the lost-sales COMDP is finite
-- statement:
--   Consider the COMDP of the lost-sales inventory model observed only at zero, under the standing assumptions. Its states are the beliefs $z$ with finite second moment (Assumption 1). For each state $z$, let $w(z)$ be the optimal average cost per period, the infimum over all policies. Then Assumption B(i) holds:
--   $$w^*:=\inf_{z}w(z)<+\infty .$$
--
--   Lemma 3 is the first of the two conditions of Assumption (B). Together with (W*) and Theorem 2, it is what Lemma 2 needs to produce a stationary average-cost optimal policy.
--
--   **Formalization Note.** Costs are in $[0,\infty]$ and the COMDP has cost lower bound $0$, so $w^*$ is the infimum of `wOpt` and the claim is $w^*\ne\infty$.
-- source:
--   Bai, Chen & Stolyar, Average Cost Optimality in Partially Observed Lost-Sales Inventory Systems, SSRN preprint 3865728, p. 12, Lemma 3

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE
open scoped ENNReal NNReal

namespace PartialLostSales.ACOI

/-- Lemma 3, p. 12: Assumption B(i), `w* = inf_z w(z) < ∞`, holds for the COMDP. -/
theorem lemma_3 (P : Params) (hP : Standing P) (M : MDP (Bel P) (Act P)) (hM : IsCOMDP P M) :
    (⨅ z, wOpt M z) ≠ ⊤ := by sorry

end PartialLostSales.ACOI
