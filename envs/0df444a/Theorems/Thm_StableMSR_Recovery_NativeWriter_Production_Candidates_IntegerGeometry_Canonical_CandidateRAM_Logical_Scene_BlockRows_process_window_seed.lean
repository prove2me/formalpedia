-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_BlockRows_process_window_seed
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.process_window_seed
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-25T05:00:55.175132+00:00
-- url     : https://prove2.me/theorems/d8eb9246-5bf3-42e9-847c-f21761f7d07d
-- title:
--   One window seed produces its exact row and updates precisely the canonical block metadata
-- statement:
--   Fix a candidate word $c=u(h+1)+g$ and a seed $p$ in its window $W$. Suppose the earlier representative mask and the earlier marked membership rows are correct. The whole source branch for $p$ fills its membership row, compares it with earlier representatives, and records its metadata if it is the first seed for its block. Specifically, the intermediate heap $H$ equals the incoming heap outside this one row and satisfies
--   $$H[\operatorname{row}(p)+q]=\mathbf1\{q\in C_p\}.$$
--   Only a representative changes the two selection masks, the block minimum, and the ownership-intersection flag as applicable. An empty representative block clears the all-nonempty flag. Output is preserved; the charged time is at most $6000(n+1)^2(h+1)$. Buffers are separated at their actual read and write addresses.
-- source:
--   Native candidate enumeration in Appendix A.6, Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_VertexBlockRows
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
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.process_window_seed
    (n h g u buf win b matrix mark rep minimum touch own vertex : ℕ)
    (m : ℤ → ℤ) (s : Logical.State) (W : Cluster n) (p : Fin n) (owner : Fin n → Fin n)
    (hp : p∈W) (hg : g<h+1)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (seed : s.reg 173=(p.val:ℤ))
    (digitsAt : s.reg 166=(buf:ℤ)) (balls : s.reg 169=(g:ℤ)) (window : s.reg 170=(win:ℤ))
    (baseAt : s.reg 165=(b:ℤ)) (matrixAt : s.reg 80=(matrix:ℤ)) (markAt : s.reg 171=(mark:ℤ))
    (repAt : s.reg 77=(rep:ℤ)) (minAt : s.reg 78=(minimum:ℤ)) (touchAt : s.reg 79=(touch:ℤ))
    (ownerAt : s.reg 72=(own:ℤ)) (vertexAt : s.reg 162=(vertex:ℤ))
    (digits : ∀ j < 2*(h+1), s.heap (buf+j)=(CartesianBallRows.digit n u j:ℤ))
    (inside : ∀ q : Fin n, 1 ≤ s.heap (win+q.val) ↔ q∈W)
    (owners : ∀ q : Fin n, s.heap (own+q.val)=((owner q).val:ℤ)) :
    let code := SingleCodes.encode h g u
    let C := rowBlock m W h code
    let R := representatives W C
    let key := b+p.val
    let dest := matrix+key*n
    (∀ q : Fin n, q∉W → s.heap (dest+q.val)=0) →
    (∀ i < p.val, 1 ≤ s.heap (mark+i) ↔ i∈R) →
    (∀ i < p.val, i∈R → ∀ q : Fin n, s.heap (matrix+(b+i)*n+q.val)=if q∈C i then 1 else 0) →
    (∀ i < n, ∀ j < 2*(h+1), dest+i ≠ buf+j) →
    (∀ i < n, ∀ j < n, dest+i ≠ win+j ∧ dest+i ≠ own+j ∧ dest+i ≠ mark+j) →
    (∀ a ∈ [mark+p.val,rep+key,minimum+key,touch+key], ∀ q : Fin n, a ≠ dest+q.val ∧ a ≠ own+q.val) →
    ∃ (t : Logical.State) (k : ℕ) (H : ℕ → ℤ), Logical.Executes n m seedWork s t k ∧
      k ≤ 6000*(n+1)^2*(h+1) ∧
      (∀ q : Fin n, H (dest+q.val)=if q∈C p.val then 1 else 0) ∧
      (∀ a, a<dest ∨ dest+n ≤ a → H a=s.heap a) ∧
      (let marked := Function.update (Function.update H (mark+p.val) 1) (rep+key) 1
       let withMin := if ne : (C p.val).Nonempty then Function.update marked (minimum+key) (((C p.val).min' ne).val:ℤ) else marked
       let committed := if ∃ q ∈ C p.val, (owner q).val=vertex then Function.update withMin (touch+key) 1 else withMin
       t.heap=if p.val∈R then committed else H) ∧
      t.reg 172=(if p.val∈R ∧ ¬(C p.val).Nonempty then 0 else s.reg 172) ∧
      t.output=s.output ∧ t.closed=s.closed
 := by sorry
