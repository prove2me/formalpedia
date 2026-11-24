-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_representative_and_piece
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.representative_and_piece
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T16:47:05.9268+00:00
-- url     : https://prove2.me/theorems/ce8eee5d-f735-45c1-adbf-dbc048e8728c
-- title:
--   The geometry program recognizes exactly the points of the selected scene part
-- statement:
--   For a scene with $n>0$ points and a slot $r$, the opening of geometry construction computes the row $u=\lfloor r/n\rfloor$, the candidate representative $i=r\bmod n$ and the integer scale unit $n^2+1$. The resulting test on a point $p$ holds exactly when the least index with the same scene label as $p$ is $i$. This also covers slots whose candidate index occurs later in a label class. With arbitrary signed scene labels and arbitrary incoming scratch space the cost is at most $$350(n+1)+20\lfloor r/n\rfloor.$$ The heap and the output stream are preserved.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.representative_and_piece (n r:ℕ) (m:ℤ→ℤ) (scene:ℕ→ℤ) (s:Logical.State)
    (hn:0<n) (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (slot:s.reg 65=(r:ℤ)) (agree:∀j:ℕ,m (j:ℤ)=scene j):
    ∃t k,Logical.Executes n m (Logical.chain ((Logical.listOf Logical.src_build_geometry).take 22)) s t k ∧
      k ≤ 350*(n+1)+20*(r/n) ∧ t.reg 189=((r/n:ℕ):ℤ) ∧ t.reg 190=((r%n:ℕ):ℤ) ∧
      t.reg 191=((3+r/n*(n+2)+2:ℕ):ℤ) ∧
      t.reg 192=m (((3+r/n*(n+2)+2:ℕ):ℤ)+(r%n:ℕ)) ∧ t.reg 195=(IntegerGeometry.unit n:ℤ) ∧
      (∀p:Fin n, p∈IntegerGeometry.Bits.piece n scene (r/n) (r%n) ↔ 1≤t.reg 193 ∧ m (t.reg 191+p.val)=t.reg 192) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by sorry
