-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_request_child_by_its_boundary
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.request_child_by_its_boundary
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T03:46:07.871855+00:00
-- url     : https://prove2.me/theorems/12a35f0d-bdb1-4e48-81e4-9f3f73366b0c
-- title:
--   Request the canonical child key from its component bitmap
-- statement:
--   For one child representative the source computes its actual graph boundary, reads the extended assignment there, encodes the canonical tight key, and emits precisely one child request. The proof gives the new scratch interval, frame and output count, and a uniform cost bound.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.request_child_by_its_boundary (d : SingleCircuit.Instance) (cursor active points edge table words maxWord : ℕ) (m : ℤ→ℤ)
    (s : Logical.State) (member : ℕ→Bool) (row : SingleCircuit.Assignment) (slot : ℕ→ℕ)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(d.n:ℤ)) (alloc : s.reg 8=(cursor:ℤ))
    (activeAt : s.reg 71=(active:ℤ)) (pointsAt : s.reg 235=(points:ℤ)) (edgeAt : s.reg 75=(edge:ℤ))
    (tableAt : s.reg 225=(table:ℤ)) (wordsAt : s.reg 76=(words:ℤ)) (ready : s.closed=false) (count : s.reg 82=(s.output.length:ℤ))
    (vertices : ∀p<d.n,s.heap (active+p)=if d.active p then 1 else 0)
    (component : ∀p<d.n,s.heap (points+p)=if member p then 1 else 0)
    (graph : ∀q<d.n,∀p<d.n,s.heap (edge+(q*d.n+p))=if d.edge q p then 1 else 0)
    (below : ∀p<d.n,active+p<cursor ∧ points+p<cursor) (edgeEnd : ∀q<d.n,∀p<d.n,edge+(q*d.n+p)<cursor) :
    let C:=(List.range d.n).filter member
    let B:=TightLanguage.rimOf d C
    (∀p∈B,table+p<cursor ∧ s.heap (table+p)=(slot p:ℤ) ∧ words+slot p<cursor ∧
      s.heap (words+slot p)=(TightLanguage.value row p:ℤ) ∧ TightLanguage.value row p ≤ maxWord) →
    ∃t k, Logical.Executes d.n m (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.countedBody (Scene.BlockRows.instruction src_trial 9)) 1)) 9)) s t k ∧
      k ≤ 700*(d.n+1)^3+600*(d.n+1)*(d.n+maxWord+1)+300+d.n*(165+6*d.n) ∧ t.reg 8=((cursor+d.n:ℕ):ℤ) ∧
      (∀p,p<cursor ∨ cursor+d.n ≤ p → t.heap p=s.heap p) ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) ∧
      t.output=s.output++[Instr.need (Naming.name (C,TightLanguage.restricted B row))] := by sorry
