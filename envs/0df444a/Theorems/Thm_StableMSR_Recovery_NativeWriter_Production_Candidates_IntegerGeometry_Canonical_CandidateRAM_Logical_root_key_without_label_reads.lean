-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_root_key_without_label_reads
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.root_key_without_label_reads
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-24T16:16:26.805915+00:00
-- url     : https://prove2.me/theorems/4b09dbee-c760-4ddb-b636-e80088c4c146
-- title:
--   A component with empty boundary has a quadratic-time canonical key for arbitrary label data
-- statement:
--   For any component bitmap on $n$ vertices, the source routine with an empty boundary computes the canonical identifier of that component with the empty assignment. The charge is at most $1000(n+1)^2$. Both label arrays may contain arbitrary signed integers. Every scratch word and the output stream are preserved.
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_LogicalCandidateProgram
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.root_key_without_label_reads (n p b v l:ℕ) (input:ℤ → ℤ) (s:Logical.State)
    (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (point:s.reg 153=(p:ℤ)) (boundary:s.reg 154=(b:ℤ))
    (index:s.reg 155=(v:ℤ)) (table:s.reg 76=(l:ℤ)) (empty:∀i<n,¬ 1 ≤ s.heap (b+i)):
    let pts:=(List.range n).filter (fun i=>decide (1 ≤ s.heap (p+i)))
    ∃t k,Logical.Executes n input Logical.src_name_key s t k ∧ k ≤ 1000*(n+1)^2 ∧
      t.reg 158=(CandidateRAM.Naming.name (pts,[]):ℤ) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by sorry
