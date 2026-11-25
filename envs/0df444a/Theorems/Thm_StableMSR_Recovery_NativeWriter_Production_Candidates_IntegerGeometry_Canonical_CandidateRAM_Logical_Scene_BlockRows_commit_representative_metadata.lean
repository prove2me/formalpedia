-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_BlockRows_commit_representative_metadata
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.commit_representative_metadata
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-25T04:56:33.886815+00:00
-- url     : https://prove2.me/theorems/403bd9b6-e008-4a07-a986-5440fef5292c
-- title:
--   Recording a selected block, its least point and its ownership flag
-- statement:
--   Once a new block $C$ has been selected, the program records its seed in the local and persistent representative masks. A nonempty block records its least point and sets its ownership flag precisely when some point of $C$ has the current vertex as owner. An empty block clears the all-nonempty flag. Under separation of the destination cells from the two input rows, all other heap changes are given by these assignments, the output is preserved, and the routine takes at most $700(n+1)$ machine steps. The result also applies when a block has several points with the given owner.
-- source:
--   Native candidate enumeration in Appendix A.6, Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_VertexBlockRows
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option maxHeartbeats 4100000
set_option maxRecDepth 35000
set_option autoImplicit false
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.commit_representative_metadata
    (n base mark rep minimum touch row own seed vertex : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (C : Cluster n) (owner : Fin n → Fin n) (selected : s.reg 177 = 1)
    (one : s.reg 6 = 1) (size : s.reg 64 = (n:ℤ)) (seedAt : s.reg 173 = (seed:ℤ))
    (baseAt : s.reg 165 = (base:ℤ)) (markAt : s.reg 171 = (mark:ℤ)) (repAt : s.reg 77 = (rep:ℤ))
    (minAt : s.reg 78 = (minimum:ℤ)) (touchAt : s.reg 79 = (touch:ℤ)) (rowAt : s.reg 176 = (row:ℤ))
    (ownerAt : s.reg 72 = (own:ℤ)) (vertexAt : s.reg 162 = (vertex:ℤ))
    (bits : ∀ q : Fin n, 1 ≤ s.heap (row+q.val) ↔ q∈C)
    (owners : ∀ q : Fin n, s.heap (own+q.val) = ((owner q).val:ℤ))
    (disjoint : ∀ a ∈ [mark+seed,rep+(base+seed),minimum+(base+seed),touch+(base+seed)],
      ∀ q : Fin n, a ≠ row+q.val ∧ a ≠ own+q.val) :
    let key := base+seed
    let marked := Function.update (Function.update s.heap (mark+seed) 1) (rep+key) 1
    let withMin := if ne : C.Nonempty then Function.update marked (minimum+key) (((C.min' ne).val):ℤ) else marked
    ∃ t k, Logical.Executes n m (instruction seedWork 8) s t k ∧ k ≤ 700*(n+1) ∧
      t.reg 172 = (if C.Nonempty then s.reg 172 else 0) ∧
      t.heap = (if ∃ q ∈ C, (owner q).val=vertex then Function.update withMin (touch+key) 1 else withMin) ∧
      t.output=s.output ∧ t.closed=s.closed
 := by sorry
