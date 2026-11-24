-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_bounded_run_is_native
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.bounded_run_is_native
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T01:23:59.371288+00:00
-- url     : https://prove2.me/theorems/259bde87-6e26-469b-986c-41d7d841f5be
-- title:
--   The checked integer execution gives a native run at twice the fuel bound
-- statement:
--   For the explicit canonical candidate generator, a successful evaluation in $F$ syntax steps yields an execution of the actual RAM in at most $2F$ instructions. The real registers, real memory and query count are preserved by restoring only the integer banks. All six incoming pointer registers are preserved.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CandidateInterpreter
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.bounded_run_is_native {n:ℕ} (d:Fin n→Fin n→ℝ) (s:Store) (h w fuel:ℕ) (t:CandidateRAM.Banks)
  (done:CandidateRAM.run fuel [CandidateRAM.code h w] (CandidateRAM.banks s)=some t) :
  ∃z,Executes d (CandidateRAM.program h w) s (CandidateRAM.restore s t) z ∧ z≤2*fuel ∧
  (∀j<6,t.reg j=s.ptrs j) := by sorry
