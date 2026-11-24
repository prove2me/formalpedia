-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_append_record_on_arbitrary_memory
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.append_record_on_arbitrary_memory
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T02:14:33.283723+00:00
-- url     : https://prove2.me/theorems/bf0cf67c-b2ea-48a1-aeaa-d10cc734a92a
-- title:
--   The concrete record writer appends any of the five instruction types
-- statement:
--   An arbitrary initial memory and registers satisfying the argument convention suffice. The program writes precisely the header and any literal bits owned by this record, preserves every other memory cell, advances the record number, and consumes at most $200+n(165+6n)$ syntax inspections. The assertion covers empty masks and all five tags.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CandidateInterpreter
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.append_record_on_arbitrary_memory
    (s:Banks) (n row base:ℕ) (e:Instr)
    (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (ord:s.reg 82=(row:ℤ))
    (tag:s.reg 218=e.tag) (arg:s.reg 219=e.arg)
    (mask:∀ms,e=.lit ms → s.reg 220=(base:ℤ) ∧
      ∀j<n,s.mem (cell 7 (base+j))=(if ms.contains j then 1 else 0)) :
    ∃t k,k ≤ 200+n*(165+6*n) ∧ run k [proc_output] s=some t ∧
      t.reg 82=((row+1:ℕ):ℤ) ∧ t.mem (inputCell 1 row)=e.tag ∧ t.mem (inputCell 2 row)=e.arg ∧
      (∀ms,e=.lit ms → ∀j<n,t.mem (inputCell 3 (row*n+j))=(if ms.contains j then 1 else 0)) ∧
      ∀q,q≠inputCell 1 row → q≠inputCell 2 row →
        (e.tag=0 → ∀j<n,q≠inputCell 3 (row*n+j)) → t.mem q=s.mem q := by sorry
