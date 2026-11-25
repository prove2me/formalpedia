-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_WindowSweep_complete_vertex_menu
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep.complete_vertex_menu
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-25T05:23:56.891803+00:00
-- url     : https://prove2.me/theorems/9145d5ca-3bc3-5945-81f5-60d3b1a33c42
-- title:
--   Exact candidate tables and feasibility bit for one vertex and word
-- statement:
--   For one vertex and one candidate word $c=u(h+1)+g$, the complete per-vertex program decodes the word, initializes scratch memory, processes every seed in its window $W$, and writes the program's menu bit. With disjoint input and destination cells and initially zero permanent slot cells, the result is $$\operatorname{menu}[a,i]=\mathbf 1\{\operatorname{blocks}(W,h,c)\text{ is a partition of }W\}.$$ The selected-block masks, least points, ownership flags and membership rows have their specified values. The scratch cursor advances by $2(h+1)+n$, and the running time is at most $20000(n+1)^3(h+1)(M+u+1)$ for $M$ available word slots.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep.complete_vertex_menu
    (n h g u a M pos cursor wins own menus : ℕ) (m : ℤ → ℤ) (s : Logical.State) (L : Layout)
    (W : Cluster n) (owner : Fin n → Fin n) (hn : 0<n) (hg : g<h+1) (hu : u<CartesianBallRows.rows n (h+1))
    (base : L.base=(a*M+pos)*n) (mask : L.mask=cursor+2*(h+1))
    (one : s.reg 6=1) (zero : s.reg 7=0) (atCursor : s.reg 8=(cursor:ℤ))
    (size : s.reg 64=(n:ℤ)) (height : s.reg 68=((h+1:ℕ):ℤ)) (length : s.reg 70=(M:ℤ))
    (atOwner : s.reg 72=(own:ℤ)) (atWins : s.reg 74=(wins:ℤ))
    (rep : s.reg 77=(L.rep:ℤ)) (minAt : s.reg 78=(L.first:ℤ)) (touch : s.reg 79=(L.touch:ℤ))
    (matrixAt : s.reg 80=(L.matrix:ℤ)) (menuAt : s.reg 81=(menus:ℤ))
    (vr : s.reg 162=(a:ℤ)) (word : s.reg 163=(SingleCodes.encode h g u:ℤ)) (slot : s.reg 164=(pos:ℤ))
    (inside : ∀ q : Fin n, s.heap (wins+a*n+q.val)=if q∈W then 1 else 0)
    (owners : ∀ q : Fin n, s.heap (own+q.val)=((owner q).val:ℤ))
    (fresh : ∀ z : Cell n, (∀ p, z≠.mask p) → s.heap (L.addr z)=0)
    (below : ∀ z : Cell n, (∀ p, z≠.mask p) → L.addr z<cursor)
    (inputsBelow : ∀ q : Fin n, wins+a*n+q.val<cursor ∧ own+q.val<cursor)
    (menuDisjoint : ∀ z : Cell n, L.addr z≠menus+(a*M+pos))
    (sep : Separated n h cursor (wins+a*n) own L) :
    ∃ t k, Logical.Executes n m Logical.src_data_for_vertex s t k ∧
      k ≤ 20000*(n+1)^3*(h+1)*(M+u+1) ∧
      VertexImage L W m h (SingleCodes.encode h g u) owner a (menus+(a*M+pos)) cursor s t
 := by sorry
