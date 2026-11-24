-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_separator_neighbourhood_mask
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.separator_neighbourhood_mask
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-24T02:31:39.076594+00:00
-- url     : https://prove2.me/theorems/52d8e2e7-7d8a-459a-b811-d8447c922112
-- title:
--   The source routine computes the exact external separator neighbourhood
-- statement:
--   Given the active vertices, the point set, and a directed adjacency matrix in previously allocated scratch space, the routine returns a fresh bitmap. It marks precisely the active vertices outside the point set with an incoming edge from a point of the set. It preserves every word outside the new bitmap and the output stream, advances the allocation cursor by exactly $n$, and consumes at most $600(n+1)^3$ source charges.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.separator_neighbourhood_mask (n a p edge top:ℕ) (m:ℤ → ℤ) (s:State) (one:s.reg 6=1) (zero:s.reg 7=0)
    (size:s.reg 64=(n:ℤ)) (cursor:s.reg 8=(top:ℤ)) (active:s.reg 71=(a:ℤ))
    (point:s.reg 139=(p:ℤ)) (edges:s.reg 75=(edge:ℤ)) (aa:a+n ≤ top) (pp:p+n ≤ top) (ee:edge+n*n ≤ top):
    ∃t k,Executes n m src_rim s t k ∧ k ≤ 600*(n+1)^3 ∧ t.reg 143=(top:ℤ) ∧
      t.reg 8=((top+n:ℕ):ℤ) ∧ (∀i<n,t.heap (top+i)=if (1 ≤ s.heap (a+i) ∧ ¬1 ≤ s.heap (p+i)) ∧ (∃j<n,1 ≤ s.heap (p+j) ∧ 1 ≤ s.heap (edge+(j*n+i))) then 1 else 0) ∧
      (∀q,q<top ∨ top+n ≤ q → t.heap q=s.heap q) ∧ t.output=s.output ∧ t.closed=s.closed := by sorry
