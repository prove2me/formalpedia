-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_NetRAM_greedy_net_bitmap
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM.greedy_net_bitmap
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T17:26:54.407341+00:00
-- url     : https://prove2.me/theorems/6bdcd85c-419f-4fbf-939a-5b5e2e7862f7
-- title:
--   The geometry program constructs the exact greedy net and scene part in the initialized arrays
-- statement:
--   Let $W$ be the part of a scene selected by a regional slot on $n>0$ points, and put $U=n^2+1$. Sweeping the points of $W$ in increasing order, keep $p$ exactly when every earlier retained point $z$ satisfies $m(p,z)>2U$ in the integer rank array. The first 23 top-level commands of geometry construction write the characteristic functions of this greedy net and of $W$ at their two initialized addresses. They preserve the tape and all other scratch words. If $C=n+k+S+1$ is the capacity for $S$ scene rows, their charge is at most $$350C+601(n+1)^3.$$
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_InitializedSeparatorTraversal
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.NetRAM.greedy_net_bitmap (x:World) (m:Store) (r h w:ℕ) (s:Logical.State)
    (hn:0 < x.n) (hr:r < x.rows*x.n) (ready:Ready x m) (prepared:Logical.Prepared x.n r h w s):
    let o:=Logical.offsets x.n (Logical.sizes x.n h)
    let W:=WindowProfiles.piece x (r/x.n) (r%x.n)
    ∃t k,Logical.Executes x.n m.imem (Logical.chain ((Logical.listOf Logical.src_build_geometry).take 23)) s t k ∧
      k ≤ 350*x.cap+601*(x.n+1)^3 ∧
      (∀p:Fin x.n,t.heap (Logical.cursorAt o 0+p.val)=if p∈IntegerGeometry.Bits.net m.imem W then 1 else 0) ∧
      (∀p:Fin x.n,t.heap (Logical.cursorAt o 2+p.val)=if p∈W then 1 else 0) ∧
      (∀q,(q < Logical.cursorAt o 0 ∨ Logical.cursorAt o 0+x.n ≤ q) →
        (q < Logical.cursorAt o 2 ∨ Logical.cursorAt o 2+x.n ≤ q) → t.heap q=s.heap q) ∧ t.output=s.output ∧ t.closed=s.closed := by sorry
