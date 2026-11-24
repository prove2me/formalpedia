-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_unfiltered_scan_is_exact
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.unfiltered_scan_is_exact
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T23:37:28.053763+00:00
-- url     : https://prove2.me/theorems/2a0e4587-bc9e-41ce-92e4-1602b0b8a943
-- title:
--   Scanning every pivot recovers exactly the accepted ordered productions
-- statement:
--   For any finite separator instance $d$, width $w$, and injective numerical naming of tight keys, let $U(d,w)$ be the tape of all pivot and menu-label candidates. If $C(d,w)$ is the ordered stream of accepted separator productions, including its exit handle, then $$\operatorname{eval}(U(d,w))=C(d,w).$$ This identifies every emitted mask, child handle, alternative predecessor, and final handle, including missing children and repeated row keys.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.unfiltered_scan_is_exact (enc:Key→ℕ)
    (inj:Function.Injective enc) (d:Instance) (w:ℕ) :
    Candidates.eval (tape enc d w)=⟨(chart d w).1,((chart d w).2:ℤ)⟩ := by sorry
