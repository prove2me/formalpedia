-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_regional_production_size
-- name    : StableMSR.Recovery.NativeWriter.Production.regional_production_size
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T23:13:16.763708+00:00
-- url     : https://prove2.me/theorems/128b1211-f54d-43f7-a204-e40e5f741d89
-- title:
--   Exact size bound for the ordered regional production stream
-- statement:
--   For every region slot in an $n$-point scene with $n\ge 2$ and $0<\varepsilon<1$, decoding its symbolic stream reconstructs the required gate packet and signed root token. The number $T$ of events satisfies $$T\le n^{75E(\varepsilon)}.$$ The bound includes unsuccessful root lookups and both kinds of empty slots.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_RegionalProductionTable
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

theorem StableMSR.Recovery.NativeWriter.Production.regional_production_size (x : World) (e : ℚ) (r:ℕ)
    (he:0<e) (hl:e<1) (hn:2≤x.n) :
    let h:=budget (e:ℝ)
    let w:=widthBound (e:ℝ)
    let t:=regionalScript x h w r
    t.packet=Relative.packet x h w r ∧ t.events.length≤x.n^(75*parameterEnvelope (e:ℝ)) := by sorry
