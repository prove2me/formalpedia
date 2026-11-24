-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_scratch_allocation_exact
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.scratch_allocation_exact
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T01:28:42.841305+00:00
-- url     : https://prove2.me/theorems/f8fd08c7-49e7-42f3-a3c6-5007366a9729
-- title:
--   The candidate program allocates and clears a scratch interval in linear time
-- statement:
--   The actual allocation routine initializes exactly the $L$ new words at the current scratch cursor $a$, returns $a$, and advances the cursor to $a+L$. Every other integer memory word retains its incoming value, including the case $L=0$. Evaluation uses at most $64(1+L)$ syntax inspections, independently of the magnitude of the scratch cursor.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CandidateInterpreter
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.scratch_allocation_exact (dst len base L:ℕ) (hd:64≤dst) (hl:64≤len) (ne:dst≠len) (s:Banks)
    (one:s.reg 6=1) (zero:s.reg 7=0) (cursor:s.reg 8=(base:ℤ)) (length:s.reg len=(L:ℤ)) :
    ∃F t,F≤64*(1+L) ∧ run F [allocate dst len] s=some t ∧ t.reg dst=(base:ℤ) ∧ t.reg 8=((base+L:ℕ):ℤ) ∧
    (∀j<L,t.mem (cell 7 (base+j))=0) ∧ ∀q:ℤ,(∀j<L,q≠cell 7 (base+j)) → t.mem q=s.mem q := by sorry
