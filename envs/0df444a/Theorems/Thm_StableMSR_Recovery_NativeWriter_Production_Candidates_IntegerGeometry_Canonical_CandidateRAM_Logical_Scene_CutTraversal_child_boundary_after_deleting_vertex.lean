-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_child_boundary_after_deleting_vertex
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.child_boundary_after_deleting_vertex
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T03:46:24.81411+00:00
-- url     : https://prove2.me/theorems/e4f3ad54-6425-5e58-a169-baa50a876061
-- title:
--   Every child-boundary label comes from the separator or the deleted vertex
-- statement:
--   When a vertex is removed from a component, every active neighbor on the boundary of a resulting child belongs to the original boundary or is the vertex just removed. Thus all labels needed for a child request are in the extended assignment.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.4 and A.6. Implementation lemma for the boundary assignment loop.

import Definitions.Def_StableMSR_RegionalMenuImage
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.child_boundary_after_deleting_vertex (d : SingleCircuit.Instance) (parent : List ℕ) (v child : ℕ)
    (bounded : parent.toFinset.card ≤ d.n) (seed : child∈parent.erase v) :
    let C:=TightLanguage.pieceAt d (parent.erase v) child
    ∀p∈TightLanguage.rimOf d C,p=v ∨ p∈TightLanguage.rimOf d parent := by sorry
