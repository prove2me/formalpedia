-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_WindowSweep_complete_seed_sweep
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep.complete_seed_sweep
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-25T05:24:18.412721+00:00
-- url     : https://prove2.me/theorems/aacb801f-e2b7-484f-b712-35e0fd3ca954
-- title:
--   Complete window sweep over all possible block seeds
-- statement:
--   Fix an $n$-point window $W$, a candidate word $c=u(h+1)+g$ with $0\le g\le h$, and an owner for every point. Initialize the seed tables to zero, place the input arrays in disjoint cells, and start the all-nonempty flag at one. The complete loop returns the exact representative masks, minima, ownership intersections and membership rows for every seed, with the correct all-nonempty flag. Points outside the window leave their rows at zero. Its cost is at most $$6200(n+1)^3(h+1).$$ Every heap cell outside the slot and the output stream are preserved.
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_WindowSweep
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
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep.complete_seed_sweep
    (n h g u buf win own vertex : ℕ) (m : ℤ → ℤ) (s : Logical.State) (L : Layout)
    (W : Cluster n) (owner : Fin n → Fin n) (hg : g < h+1)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (digitsAt : s.reg 166=(buf:ℤ))
    (balls : s.reg 169=(g:ℤ)) (window : s.reg 170=(win:ℤ)) (b : s.reg 165=(L.base:ℤ))
    (matrixAt : s.reg 80=(L.matrix:ℤ)) (mask : s.reg 171=(L.mask:ℤ)) (rep : s.reg 77=(L.rep:ℤ))
    (minAt : s.reg 78=(L.first:ℤ)) (touch : s.reg 79=(L.touch:ℤ))
    (ownerAt : s.reg 72=(own:ℤ)) (vertexAt : s.reg 162=(vertex:ℤ))
    (digits : ∀ j < 2*(h+1), s.heap (buf+j)=(CartesianBallRows.digit n u j:ℤ))
    (inside : ∀ q : Fin n, 1 ≤ s.heap (win+q.val) ↔ q∈W)
    (owners : ∀ q : Fin n, s.heap (own+q.val)=((owner q).val:ℤ))
    (empty : ∀ z : Cell n, s.heap (L.addr z)=0) (initialFlag : s.reg 172=1)
    (sep : Separated n h buf win own L) :
    ∃ t k, Logical.Executes n m seedLoop s t k ∧ k ≤ 6200*(n+1)^3*(h+1) ∧
      Image L W (rowBlock m W h (SingleCodes.encode h g u)) owner vertex n s t
 := by sorry
