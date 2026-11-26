-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_bounded_stream_evaluation
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.bounded_stream_evaluation
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T02:17:16.244537+00:00
-- url     : https://prove2.me/theorems/bf58205e-c8b5-407b-881f-0ff51f5808a6
-- title:
--   The separator loops produce the canonical list within the uniform time bound
-- statement:
--   Execute the fixed source program on each live representative slot. It must return the canonical list of literals, child requests, consistency bits, row seals and final marker, and close the list, within $c\\,\\mathrm{cap}^D n^{b E(\\varepsilon)}$ source charges. Arithmetic macros act directly on integers, scratch storage has natural indices, and each output operation appends a typed record.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_LogicalCandidateProgram
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.bounded_stream_evaluation :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Logical.Executes x.n s.imem (Logical.candidate (budget (e:ℝ)) (widthBound (e:ℝ)))
       (Logical.initial (CandidateRAM.banks s)) t z ∧ z ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
       t.closed=true ∧ t.output=tape CandidateRAM.Naming.name
         (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ)) := by sorry
