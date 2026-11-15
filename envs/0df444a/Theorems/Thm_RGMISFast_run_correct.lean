-- Prove2me | Theorems.Thm_RGMISFast_run_correct
-- name    : RGMISFast.run_correct
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T01:27:54.848461+00:00
-- url     : https://prove2.me/theorems/7d8bdf43-b27b-4cc1-8b56-33900f9bc885
-- title:
--   Correctness of the memoized execution and its recorded answers
-- statement:
--   For every finite ordered graph, every real rank vector r and every root u, the memoized execution returns the greedy-MIS answer, and every recorded memo-table answer is correct. $$\mathrm{run}(u).\mathrm{answer}=\mathrm{inMIS}(u).$$ Ties are resolved by the fixed vertex order. This is the correctness clause of Observation 2.2, generalized to all real rank vectors.
-- source:
--   Randomized Greedy MIS Is Fast at Every Node, Observation 2.2 p.11, Appendix B p.30; explicit operational correctness/counting clause. Generalized by omitting unused distinctness and nonnegativity assumptions.

import Definitions.Def_RGMISFast_tau
open RGMISFast
set_option autoImplicit false

theorem RGMISFast.run_correct {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (r : V → ℝ) :
    (∀ v b, (run G r u).2.memo v = some b → b = inMIS G r v) ∧
    (run G r u).1 = inMIS G r u := by sorry
