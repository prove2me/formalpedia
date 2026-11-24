-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_unfiltered_candidate_bound
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.unfiltered_candidate_bound
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T23:38:00.756923+00:00
-- url     : https://prove2.me/theorems/fd511b36-7861-4915-a5cc-a9da88d961b4
-- title:
--   The full candidate tape obeys the stability exponent before filtering
-- statement:
--   Let $d$ be the numerical separator instance of a region of an $n$-point scene. For $n\ge2$ and $0<\varepsilon<1$, let $M$ count every candidate instruction, including losing pivots, missing children, locally rejected labels, row installations, and root lookups. Uniformly in the scene, the region, and the naming of tight keys, $$M\le n^{75E(\varepsilon)}.$$
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.unfiltered_candidate_bound
    (x:World) (u i:ℕ) (e:ℚ) (enc:Key→ℕ) (he:0<e) (hl:e<1) (hn:2≤x.n) :
    let d:=SingleCodes.instanceOf x (WindowProfiles.piece x u i) (scale x u) (budget (e:ℝ))
    (tape enc d (widthBound (e:ℝ))).length≤x.n^(75*parameterEnvelope (e:ℝ)) := by sorry
