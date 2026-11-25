-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_ComponentScan_connected_component_bitmap
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.ComponentScan.connected_component_bitmap
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-25T12:14:14.392394+00:00
-- url     : https://prove2.me/theorems/5882cb27-569e-5e37-a57a-9bfb3e3a7ea0
-- title:
--   The separator program marks exactly the component of its seed
-- statement:
--   Take any allowed seed and a directed adjacency matrix on n vertices. Starting from the seed alone, the compiled in-place marking routine computes exactly the ordered reference component through the allowed vertices. It allocates precisely n words, preserves the rest of memory and the output stream, and uses at most 800(n+1)^4 source steps.
-- source:
--   S. Ravichandran and L. Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix A.4 and A.6. Implementation lemma for the mission’s regional separator compiler.

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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.ComponentScan.connected_component_bitmap (d : Instance) (allow : ℕ→Bool) (base active edge seed : ℕ) (m : ℤ→ℤ)
    (s : State) (hs : seed<d.n) (enabled : allow seed=true)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(d.n:ℤ))
    (allocation : s.reg 8=(base:ℤ)) (seedAt : s.reg 133=(seed:ℤ))
    (allowedAt : s.reg 132=(active:ℤ)) (mat : s.reg 75=(edge:ℤ))
    (activeBelow : ∀p<d.n,active+p<base) (activeBit : ∀p<d.n,s.heap (active+p)=if allow p then 1 else 0)
    (edgeBelow : ∀q<d.n,∀p<d.n,edge+(q*d.n+p)<base)
    (edges : ∀q<d.n,∀p<d.n,s.heap (edge+(q*d.n+p))=if d.edge q p then 1 else 0) :
    ∃t k, Executes d.n m src_component s t k ∧ k≤800*(d.n+1)^4 ∧
      t.reg 138=(base:ℤ) ∧ t.reg 8=((base+d.n:ℕ):ℤ) ∧
      (∀p<d.n,t.heap (base+p)=if p∈TightLanguage.pieceAt d ((List.range d.n).filter allow) seed then 1 else 0) ∧
      (∀j,j<base ∨ base+d.n≤j → t.heap j=s.heap j) ∧ t.output=s.output ∧ t.closed=s.closed := by sorry
