-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_key_digit_routine_exact
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.key_digit_routine_exact
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T01:28:12.579471+00:00
-- url     : https://prove2.me/theorems/b5b2b7b4-b9b1-448a-aed8-39664d147ce3
-- title:
--   The exhibited key routine charges the digit and preserves the whole memory
-- statement:
--   Appending digit $z$ to the accumulated key $a$ computes $2^z(2a+1)$ in the enumerator’s actual register routine. It consumes at most $48(1+z)$ syntax steps and leaves integer memory unchanged. Its running time is uniform in the size of the accumulated key.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CandidateInterpreter
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.key_digit_routine_exact (s:Banks) (a digit:ℕ) (value:s.reg 128=(a:ℤ)) (arg:s.reg 129=(digit:ℤ)) :
    ∃F t,F≤48*(1+digit) ∧ run F [proc_code_name_push] s=some t ∧
      t.reg 131=(Naming.push a digit:ℤ) ∧ t.mem=s.mem := by sorry
