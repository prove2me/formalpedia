-- Prove2me | Theorems.Thm_RGMISFast_query_measurable_rank_regular
-- name    : RGMISFast.query_measurable_rank_regular
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T00:46:23.625203+00:00
-- url     : https://prove2.me/theorems/51be308a-e292-4f0f-8f92-060a18eae69f
-- title:
--   Measurability of the query counter and almost sure regularity of exponential ranks
-- statement:
--   For a finite ordered vertex set and a simple graph, the fresh-call counter Q of Procedure 1.1 is measurable as a function of the real ranks. Under independent Exp(1) ranks, almost surely all ranks are distinct and nonnegative.
--
--   $$Q: \mathbb R^V\to\mathbb N\text{ is measurable},\qquad \Pr[ r\text{ injective and } r\ge0]=1.$$
--
--   This supplies the measure-theoretic interface for applying deterministic query-tree bounds. The measurability clause also covers ties, which are resolved by the fixed vertex order.
-- source:
--   Randomized Greedy MIS Is Fast at Every Node, Procedure 1.1 pp.2–3; standing rank assumptions §2 p.10; proof of Theorem 1.1 p.17. Auxiliary formalization lemma making those assumptions explicit.

import Mathlib
import Definitions.Def_RGMISFast_run
import Definitions.Def_RGMISFast_rankLaw
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem RGMISFast.query_measurable_rank_regular {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Measurable (fun r : V → ℝ => RGMISFast.Q G u r) ∧
    (∀ᵐ r ∂(RGMISFast.rankLaw V), Function.Injective r ∧ ∀ v, 0 ≤ r v) := by sorry
