-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Enumeration_component_and_literal_scans
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration.component_and_literal_scans
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T01:37:01.480194+00:00
-- url     : https://prove2.me/theorems/f3dccbe3-d057-452c-b2b4-12da172b4b7c
-- title:
--   In-place component propagation and scanning least block indices preserve both reference orders
-- statement:
--   An in-place component sweep may advance along several edges in a pass. After $n$ passes it returns the very same ordered seed component as the synchronous reference fold, even on a directed graph. Separately, scanning nonempty disjoint partition blocks by their first indices gives exactly their lexicographic merge sort, including multiplicities.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration.component_and_literal_scans :
    (∀(d:Instance) (xs:List ℕ) (v:ℕ),xs.toFinset.card≤d.n → v∈xs → 0<d.n →
      let mark:=fun (s:Finset ℕ) (u:ℕ)=>if ∃z∈s,d.edge z u=true then insert u s else s
      let out:=(List.range d.n).foldl (fun s _=>xs.foldl mark s) ({v}:Finset ℕ)
      xs.filter (fun u=>decide (u∈out))=TightLanguage.pieceAt d xs v) ∧
    ∀(n:ℕ) (rows:List (List ℕ)),(∀a∈rows,a.headD n<n) →
      (∀a∈rows,∀b∈rows,a≠b → ∀q∈a,q∉b) →
      (List.range n).flatMap (fun i=>rows.filter (fun a=>a.headD n==i))=
        rows.mergeSort (fun a b=>decide (a≤b)) := by sorry
