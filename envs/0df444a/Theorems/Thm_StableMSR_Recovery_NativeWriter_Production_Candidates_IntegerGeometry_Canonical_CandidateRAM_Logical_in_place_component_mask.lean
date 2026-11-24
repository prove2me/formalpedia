-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_in_place_component_mask
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.in_place_component_mask
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T02:41:27.569799+00:00
-- url     : https://prove2.me/theorems/bd9fc42b-27e8-461a-a357-01f499f94004
-- title:
--   The actual in-place component routine returns exactly the reference component
-- statement:
--   For a seed in the allowed set, the source routine computes the mask of its full reference component under the directed adjacency relation. Its input can be asymmetric. The scratch word containing the current vertex is both read and written during propagation. The routine uses a fresh length-$n$ buffer, preserves all other words and the output stream, and costs at most $640(n+1)^4$ charges.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.in_place_component_mask (d:Instance) (a ed top seed:ℕ) (input:ℤ → ℤ) (s:State)
    (one:s.reg 6=1) (zero:s.reg 7=0) (size:s.reg 64=(d.n:ℤ)) (cursor:s.reg 8=(top:ℤ))
    (allow:s.reg 132=(a:ℤ)) (entry:s.reg 133=(seed:ℤ)) (edges:s.reg 75=(ed:ℤ))
    (aa:a+d.n ≤ top) (ee:ed+d.n*d.n ≤ top) (hs:seed<d.n) (mark:1 ≤ s.heap (a+seed))
    (graph:∀j<d.n,∀v<d.n,1 ≤ s.heap (ed+(j*d.n+v)) ↔ d.edge j v=true):
    let vs:=(List.range d.n).filter (fun j=>decide (1 ≤ s.heap (a+j)))
    ∃t k,Executes d.n input src_component s t k ∧ k ≤ 640*(d.n+1)^4 ∧ t.reg 138=(top:ℤ) ∧
      t.reg 8=((top+d.n:ℕ):ℤ) ∧ (∀j<d.n,t.heap (top+j)=if j∈TightLanguage.pieceAt d vs seed then 1 else 0) ∧
      (∀q,q<top ∨ top+d.n ≤ q → t.heap q=s.heap q) ∧ t.output=s.output ∧ t.closed=s.closed := by sorry
