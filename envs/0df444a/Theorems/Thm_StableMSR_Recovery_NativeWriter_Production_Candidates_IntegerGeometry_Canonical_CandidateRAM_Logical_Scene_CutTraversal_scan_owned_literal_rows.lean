-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_scan_owned_literal_rows
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.scan_owned_literal_rows
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T03:37:01.215801+00:00
-- url     : https://prove2.me/theorems/8478d3c3-e0d4-597c-abf7-b955743e6405
-- title:
--   Emit the literal records in the owned-block scan
-- statement:
--   The two counted loops at the start of a vertex trial enumerate point minima and block representatives in source order. They emit one exact literal mask for each matching owned representative, preserve the heap, and update the output counter within a uniform charged-step bound.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.scan_owned_literal_rows (n M v j owner rep least matrix : ℕ) (m : ℤ→ℤ) (s : Logical.State)
    (who low : ℕ→ℕ) (marked : ℕ→Bool) (member : ℕ→ℕ→Bool)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (slots : s.reg 70=(M:ℤ))
    (vertex : s.reg 226=(v:ℤ)) (word : s.reg 227=(j:ℤ))
    (ownAt : s.reg 72=(owner:ℤ)) (repAt : s.reg 77=(rep:ℤ)) (minAt : s.reg 78=(least:ℤ))
    (matAt : s.reg 80=(matrix:ℤ)) (ready : s.closed=false) (count : s.reg 82=(s.output.length:ℤ))
    (ownership : ∀q<n,s.heap (owner+q)=(who q:ℤ))
    (reps : ∀q<n,s.heap (rep+((v*M+j)*n+q))=if marked q then 1 else 0)
    (minima : ∀q<n,marked q=true → s.heap (least+((v*M+j)*n+q))=(low q:ℤ))
    (bitmap : ∀q<n,marked q=true → ∀p<n,s.heap (matrix+(((v*M+j)*n+q)*n+p))=if member q p then 1 else 0) :
    ∃t k, Logical.Executes n m (chain ((listOf src_trial).take 5)) s t k ∧ k  ≤  500*(M+1)+500*(n+1)^4 ∧
      t.heap=s.heap ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) ∧
      t.output=s.output++(List.range n).flatMap (fun i=> if who i=v then
        (List.range n).filterMap (fun q=>if marked q && low q==i then some (Instr.lit ((List.range n).filter (member q))) else none) else []) := by sorry
