-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_lemma_2_5
-- name    : ProportionalTSP.Exact.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:35.228803+00:00
-- url     : https://prove2.me/theorems/d699cda2-5776-4040-8f34-ecd03cd89497
-- title:
--   Lemma 2.5 — Generic tight graphs are forests
-- statement:
--   For a generic real cross-edge matrix $w$, every real price vector $a$ gives an acyclic tight graph:
--   $$F(a)\text{ is a forest}.$$
--   All minimizing edges at a right vertex are retained. This statement controls the entire tight graph, not one chosen assignment.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Lemma 2.5, PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem lemma_2_5 {m k : ℕ} [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (w : Fin m → Fin k → ℝ) (hw : Generic w) (a : Fin m → ℝ) :
    (tightGraph w a).IsAcyclic := by sorry

end ProportionalTSP.Exact
