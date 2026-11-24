-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Enumeration_ordered_loops_and_trial_bound
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration.ordered_loops_and_trial_bound
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T01:35:56.506364+00:00
-- url     : https://prove2.me/theorems/17aa042b-7f9d-4d31-8cfe-763598d0b42d
-- title:
--   The native traversal order realizes the exact cut and assignment lists within the raw trial bound
-- statement:
--   The descending-child preorder agrees with the exclude-first cut recurrence, and reverse quotient/remainder decoding followed by feasibility filtering gives the prescribed ordered product of menus. All outer size, cut, seed, boundary-ordinal, pivot and pivot-label attempts, including rejected raw ordinals, fit the product bound $n^{30 E(\varepsilon)}$.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_SeparatorLoopOrder
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration.ordered_loops_and_trial_bound :
    (∀(vs:List ℕ) (w:ℕ),preorder vs w=TightLanguage.cuts vs w) ∧
    (∀(d:Instance) (vs:List ℕ) (M:ℕ),0<M → ∀(valid:ℕ→ℕ→Bool) (name:ℕ→ℕ),
      (∀v,d.menu v=((List.range M).filter (valid v)).map name) →
      (((List.range (M^vs.length)).map (readBack M vs.reverse)).filter (admissible valid)).map
        (fun a=>a.map fun q=>(q.1,name q.2))=TightLanguage.assignments d vs) ∧
    ∀(n:ℕ) (e:ℚ),2≤n → 0<e → e<1 →
      let H:=budget (e:ℝ)+1
      let t:=min (widthBound (e:ℝ)) n
      let M:=H*n^(2*H)
      n*((n+1)^t*(n*(M^t*(n*M))))≤n^(30*parameterEnvelope (e:ℝ)) := by sorry
