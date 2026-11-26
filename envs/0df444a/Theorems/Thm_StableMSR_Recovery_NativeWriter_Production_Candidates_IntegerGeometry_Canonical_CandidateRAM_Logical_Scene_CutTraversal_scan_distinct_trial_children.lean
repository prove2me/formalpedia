-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_scan_distinct_trial_children
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.scan_distinct_trial_children
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T03:51:09.796353+00:00
-- url     : https://prove2.me/theorems/95118f83-599d-4578-861d-a692568ca6a3
-- title:
--   Scan all child components and request each canonical key once
-- statement:
--   From a represented vertex-deletion bitmap, execute the full trial child-search loop. Compute a connected component and its minimum at each permitted seed, issue requests only at component minima, and obtain exactly the reference list of child keys in order.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.scan_distinct_trial_children (d : SingleCircuit.Instance) (cursor allowed active edge table words maxWord : ℕ) (m : ℤ→ℤ)
    (s : Logical.State) (enabled : ℕ→Bool) (row : SingleCircuit.Assignment) (slot : ℕ→ℕ)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(d.n:ℤ)) (alloc : s.reg 8=(cursor:ℤ))
    (allowAt : s.reg 230=(allowed:ℤ)) (activeAt : s.reg 71=(active:ℤ)) (edgeAt : s.reg 75=(edge:ℤ))
    (tableAt : s.reg 225=(table:ℤ)) (wordsAt : s.reg 76=(words:ℤ)) (ready : s.closed=false) (count : s.reg 82=(s.output.length:ℤ))
    (allowBits : ∀p<d.n,allowed+p<cursor ∧ s.heap (allowed+p)=if enabled p then 1 else 0)
    (activeBits : ∀p<d.n,active+p<cursor ∧ s.heap (active+p)=if d.active p then 1 else 0)
    (edges : ∀q<d.n,∀p<d.n,edge+(q*d.n+p)<cursor ∧ s.heap (edge+(q*d.n+p))=if d.edge q p then 1 else 0) :
    let U:=(List.range d.n).filter enabled
    (∀seed∈U,∀p∈TightLanguage.rimOf d (TightLanguage.pieceAt d U seed),table+p<cursor ∧ s.heap (table+p)=(slot p:ℤ) ∧
      words+slot p<cursor ∧ s.heap (words+slot p)=(TightLanguage.value row p:ℤ) ∧ TightLanguage.value row p ≤ maxWord) →
    ∃t k,Logical.Executes d.n m (Scene.BlockRows.instruction src_trial 9) s t k ∧
      k ≤ 9+d.n*(1600*(d.n+1)^4+700*(d.n+1)*(d.n+maxWord+1)+505) ∧
      s.reg 8 ≤ t.reg 8 ∧ (∀p<cursor,t.heap p=s.heap p) ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) ∧
      t.output=s.output++(TightLanguage.parts d U).map (fun C=>Instr.need (Naming.name (C,TightLanguage.restricted (TightLanguage.rimOf d C) row))) := by sorry
