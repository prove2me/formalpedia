-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_SeparatorKeys_name_key_from_tables
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorKeys.name_key_from_tables
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-25T05:41:31.907089+00:00
-- url     : https://prove2.me/theorems/3f6762ea-6858-524a-9a7b-c0999ed6a6fb
-- title:
--   The separator program computes the canonical tight-key name from bitmap and word tables
-- statement:
--   Given the component bitmap, boundary bitmap, boundary word-slot table, and candidate words, the actual separator naming program returns the canonical integer name of the component and its ordered boundary assignment. It scans both bitmaps in increasing vertex order, inserting the delimiter between the point list and the boundary pairs. The RAM charge is at most $600(n+1)(n+B+1)$ when the word at every selected slot is at most $B$. The call preserves the heap, allocation cursor and output.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorKeys.name_key_from_tables
    (n points boundary table words maxWord : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (isPoint isBoundary : ℕ → Bool) (slot label : ℕ → ℕ)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ))
    (pointsAt : s.reg 153=(points:ℤ)) (boundaryAt : s.reg 154=(boundary:ℤ))
    (valuesAt : s.reg 155=(table:ℤ)) (wordsAt : s.reg 76=(words:ℤ))
    (pointBits : ∀ j < n, 1 ≤ s.heap (points+j) ↔ isPoint j=true)
    (boundaryBits : ∀ j < n, 1 ≤ s.heap (boundary+j) ↔ isBoundary j=true)
    (slots : ∀ j < n,isBoundary j=true → s.heap (table+j)=(slot j:ℤ))
    (labels : ∀ j < n,isBoundary j=true → s.heap (words+slot j)=(label j:ℤ))
    (bounded : ∀ j < n,isBoundary j=true → label j ≤ maxWord) :
    let ps := (List.range n).filter isPoint
    let bs := ((List.range n).filter isBoundary).map (fun j => (j,label j))
    ∃ t k, Logical.Executes n m Logical.src_name_key s t k ∧
      k ≤ 600*(n+1)*(n+maxWord+1) ∧ t.reg 158=(Naming.name (ps,bs):ℤ) ∧
      t.heap=s.heap ∧ t.reg 8=s.reg 8 ∧ t.output=s.output ∧ t.closed=s.closed
 := by sorry
