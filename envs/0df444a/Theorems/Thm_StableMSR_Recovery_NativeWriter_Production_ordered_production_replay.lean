-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_ordered_production_replay
-- name    : StableMSR.Recovery.NativeWriter.Production.ordered_production_replay
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T23:07:43.08134+00:00
-- url     : https://prove2.me/theorems/6c6df618-1849-42f0-917e-6818e123962c
-- title:
--   Event replay reconstructs the exact separator gate array and its root
-- statement:
--   For every finite numerical separator instance $d$ and every width $w$, let $A(d,w)$ be the ordered stream of accepted productions with event-indexed references. Let $R$ replay its literal, child, union, and root instructions. Then $$R(A(d,w))=\operatorname{compileRegion}(d,w).$$ Equality includes the complete ordered array, the literal masks in their supplied order, both predecessors of every binary gate, and the final root address.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_SeparatorProductionEvents
open StableMSR.Recovery.SingleCircuit StableMSR.Recovery.NativeWriter.Production

theorem StableMSR.Recovery.NativeWriter.Production.ordered_production_replay (d : Instance) (w : ℕ) :
    result (chart d w)=compileRegion d w := by sorry
