-- Prove2me | Theorems.Thm_RGMISFast_count_eq_fresh_trace
-- name    : RGMISFast.count_eq_fresh_trace
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T01:27:55.041233+00:00
-- url     : https://prove2.me/theorems/eb6d74f5-3fce-4246-8bb1-5d3890a736dc
-- title:
--   The query counter equals the number of fresh trace events
-- statement:
--   For every finite ordered graph, root u and real rank vector r, $$Q(u)=|\{e\in\mathrm{trace}(u):e.\mathrm{fresh}\}|.$$ This is an equality of the operational counter with the length of the fresh-event list, including multiplicity. It does not assert distinctness of fresh callees. It supplies the counting clause of Observation 2.2.
-- source:
--   Randomized Greedy MIS Is Fast at Every Node, Observation 2.2 p.11, Appendix B p.30; explicit operational correctness/counting clause. Generalized by omitting unused distinctness and nonnegativity assumptions.

import Definitions.Def_RGMISFast_tau
open RGMISFast
set_option autoImplicit false

theorem RGMISFast.count_eq_fresh_trace {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (r : V → ℝ) :
    (((run G r u).2.trace.filter (fun e => e.fresh)).map (fun e => e.callee)).length = Q G u r := by sorry
