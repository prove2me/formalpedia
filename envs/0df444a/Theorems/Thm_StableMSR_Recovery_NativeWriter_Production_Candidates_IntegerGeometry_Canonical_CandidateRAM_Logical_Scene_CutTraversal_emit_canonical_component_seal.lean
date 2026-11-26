-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_emit_canonical_component_seal
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.emit_canonical_component_seal
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T03:01:14.346342+00:00
-- url     : https://prove2.me/theorems/40a12a1e-8baa-54b6-a56a-5eb9f6f997a9
-- title:
--   Write the canonical seal of a component and its boundary assignment
-- statement:
--   Given the component and boundary bitmaps and a word index for each boundary vertex, the closing source block appends the seal carrying their canonical key. It increments the output count, preserves the heap and enclosing control registers, and has an explicit cost bound.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.4 and A.6. Implementation lemma for the boundary assignment loop.

import Definitions.Def_StableMSR_FeasibleEntryEmission
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

open Scene.CutTraversal

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.emit_canonical_component_seal (n points boundary table words maxWord : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (isPoint isBoundary : ℕ → Bool) (slot label : ℕ → ℕ)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (count : s.reg 82=(s.output.length:ℤ)) (open_ : s.closed=false)
    (pointsAt : s.reg 247=(points:ℤ)) (boundaryAt : s.reg 241=(boundary:ℤ))
    (valuesAt : s.reg 250=(table:ℤ)) (wordsAt : s.reg 76=(words:ℤ))
    (pointBits : ∀ j < n, 1 ≤ s.heap (points+j) ↔ isPoint j=true)
    (boundaryBits : ∀ j < n, 1 ≤ s.heap (boundary+j) ↔ isBoundary j=true)
    (slots : ∀ j < n,isBoundary j=true → s.heap (table+j)=(slot j:ℤ))
    (labels : ∀ j < n,isBoundary j=true → s.heap (words+slot j)=(label j:ℤ))
    (bounded : ∀ j < n,isBoundary j=true → label j ≤ maxWord) :
    let key := Naming.name ((List.range n).filter isPoint,((List.range n).filter isBoundary).map (fun j => (j,label j)))
    ∃ t k, Logical.Executes n m (chain ((listOf emitFeasible).drop 1)) s t k ∧
      k ≤ 700*(n+1)*(n+maxWord+1)+300+n*(165+6*n) ∧ t.heap=s.heap ∧ t.closed=false ∧
      t.output=s.output++[Instr.seal key] ∧ t.reg 82=(t.output.length:ℤ) ∧
      ∀r, r≤81 ∨ r∈[241,242,243,247,250,251,1085] → t.reg r=s.reg r := by sorry
