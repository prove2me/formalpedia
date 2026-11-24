-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_scanned_key_is_canonical
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.scanned_key_is_canonical
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T02:53:21.896156+00:00
-- url     : https://prove2.me/theorems/4504dfc2-f6bf-4be7-a490-01cf6c51c150
-- title:
--   The full source scan computes the exact canonical component-boundary key
-- statement:
--   Scan the marked component vertices, append the zero delimiter, then scan the marked boundary vertices and their assigned labels. The full source procedure returns precisely the canonical injective name for this key. When the scanned labels are at most $L$, its charge is at most $1000(n+1)(n+L+1)$, independently of the numeric size of the resulting key. The scratch and output arrays are preserved.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.scanned_key_is_canonical  (n p b v l L:ℕ) (input:ℤ → ℤ) (s:Logical.State)
  (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (point:s.reg 153=(p:ℤ)) (boundary:s.reg 154=(b:ℤ))
  (index:s.reg 155=(v:ℤ)) (table:s.reg 76=(l:ℤ)) (values:∀i<n,0 ≤ s.heap (v+i))
  (labels:∀i<n,0 ≤ s.heap (l+(s.heap (v+i)).toNat)) (limit:∀i<n,(s.heap (l+(s.heap (v+i)).toNat)).toNat ≤ L):
  let pts:=(List.range n).filter (fun i=>decide (1 ≤ s.heap (p+i)))
  let sep:=(List.range n).filter (fun i=>decide (1 ≤ s.heap (b+i)))
  let pairs:=sep.map (fun i=>(i,(s.heap (l+(s.heap (v+i)).toNat)).toNat))
  ∃t k,Logical.Executes n input Logical.src_name_key s t k ∧ k ≤ 1000*(n+1)*(n+L+1) ∧
    t.reg 158=(CandidateRAM.Naming.name (pts,pairs):ℤ) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by sorry
