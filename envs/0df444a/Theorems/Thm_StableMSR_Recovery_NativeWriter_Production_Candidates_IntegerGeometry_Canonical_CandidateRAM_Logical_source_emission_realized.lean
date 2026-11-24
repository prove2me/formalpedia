-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_source_emission_realized
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.source_emission_realized
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-24T02:16:57.543454+00:00
-- url     : https://prove2.me/theorems/06e47f0c-39f2-4856-900e-448812b8eb1e
-- title:
--   Each complete source execution produces its entire stream on the native tape
-- statement:
--   For the fixed separator program and arbitrary initial registers and memory, every terminating source execution that closes its output list gives a successful execution of the original concrete integer code. Its syntax-step count is bounded by the source charge. The header and all records encode exactly the emitted list, and all memory outside the two designated lanes is preserved.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.source_emission_realized (n h w:ℕ) (s:CandidateRAM.Banks) (t:Logical.State) (charge:ℕ)
    (valid:Logical.Executes n s.mem (Logical.candidate h w) (Logical.initial s) t charge)
    (closed:t.closed=true) :
    ∃k u,k ≤ charge ∧ CandidateRAM.run k [CandidateRAM.code h w] s=some u ∧
      (∀q:ℤ,(∀i:ℕ,q≠cell 5 i ∧ q≠cell 7 i) → u.mem q=s.mem q) ∧ Candidates.Input n u.mem t.output := by sorry
