-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_bounded_tape_evaluation
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.bounded_tape_evaluation
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-24T01:23:49.727849+00:00
-- url     : https://prove2.me/theorems/2db4074e-2674-4206-8487-0aa59e2a4415
-- title:
--   Bounded evaluation of the specified canonical separator program
-- statement:
--   Run the fully specified integer enumerator on a live representative slot. Show that some $F\le c\,\mathrm{cap}^D n^{bE(\varepsilon)}$ syntax steps suffice, that only its output and scratch lanes change, and that the records equal the canonical tape with the stated key names. This is a correctness and running-time claim about one explicit program, with no search for an implementation or a block order.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CandidateInterpreter
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.bounded_tape_evaluation :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃F t,F≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    CandidateRAM.run F [CandidateRAM.code (budget (e:ℝ)) (widthBound (e:ℝ))] (CandidateRAM.banks s)=some t ∧
    (∀q:ℤ,(∀i:ℕ,q≠cell 5 i ∧ q≠cell 7 i) → t.mem q=s.imem q) ∧
    Candidates.Input x.n t.mem (tape CandidateRAM.Naming.name (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ))) := by sorry
