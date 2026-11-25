-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_SeparatorRows_component_rim_bitmap
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorRows.component_rim_bitmap
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-25T05:47:04.522813+00:00
-- url     : https://prove2.me/theorems/6a71cc36-b7fa-41bf-8fca-49426305f76e
-- title:
--   The separator routine computes the external boundary of a component
-- statement:
--   Starting with the active-vertex bitmap, a component bitmap, and an adjacency matrix below the allocation cursor, the separator routine allocates a fresh row and computes the component's external boundary. Its bit for $p$ is one precisely when $p$ is active, lies outside the component, and some component point $q$ has an edge to $p$. The input may be a directed graph. The result holds also for an empty component or a zero-size arena. The routine preserves every other heap cell and the output and uses at most $700(n+1)^3$ charged steps.
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
set_option maxHeartbeats 4100000
set_option maxRecDepth 35000
set_option autoImplicit false

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorRows.component_rim_bitmap
    (n cursor active points edge : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (enabled member : ℕ → Bool) (adj : ℕ → ℕ → Bool)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(n:ℤ)) (allocation : s.reg 8=(cursor:ℤ))
    (activeAt : s.reg 71=(active:ℤ)) (pointsAt : s.reg 139=(points:ℤ)) (edgeAt : s.reg 75=(edge:ℤ))
    (vertices : ∀ p < n,s.heap (active+p)=if enabled p then 1 else 0)
    (component : ∀ p < n,s.heap (points+p)=if member p then 1 else 0)
    (graph : ∀ q < n,∀ p < n,s.heap (edge+(q*n+p))=if adj q p then 1 else 0)
    (below : ∀ p < n,active+p < cursor ∧ points+p < cursor)
    (graphBelow : ∀ q < n,∀ p < n,edge+(q*n+p) < cursor) :
    ∃ t k, Logical.Executes n m Logical.src_rim s t k ∧ k ≤ 700*(n+1)^3 ∧
      t.reg 143=(cursor:ℤ) ∧ t.reg 8=((cursor+n:ℕ):ℤ) ∧
      (∀ p < n,t.heap (cursor+p)=
        if enabled p=true ∧ member p=false ∧ ∃ q < n,member q=true ∧ adj q p=true then 1 else 0) ∧
      (∀ z,z < cursor ∨ cursor+n ≤ z → t.heap z=s.heap z) ∧ t.output=s.output ∧ t.closed=s.closed
 := by sorry
