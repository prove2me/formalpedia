-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_emit_canonical_owned_literals
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.emit_canonical_owned_literals
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T03:41:30.524546+00:00
-- url     : https://prove2.me/theorems/1f1bfe0a-ee84-44f3-a4d9-22370e795532
-- title:
--   Emit the owned blocks in canonical order for a feasible regional label
-- statement:
--   For a permitted word slot, the actual initial portion of a vertex trial emits precisely the canonical owned blocks of that label. This proof connects the ownership, minimum, and membership tables to the geometric partition and proves the exact output order.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.emit_canonical_owned_literals {n : ℕ} (m : ℤ→ℤ) (W : Cluster n) (h : ℕ) (v : Fin n) (j : ℕ) (u g z s : Logical.State)
    (geo : Scene.GeometryImage m W h u g) (menus : Scene.RegionalMenus m W h g z) :
    let M:=sizes n h
    let o:=offsets n M
    ∀ (_ : j<M), 1 ≤ s.heap (cursorAt o 10+(v.val*M+j)) →
    s.reg 6=1 → s.reg 64=(n:ℤ) → s.reg 70=(M:ℤ) → s.reg 226=(v.val:ℤ) → s.reg 227=(j:ℤ) →
    s.reg 72=(cursorAt o 1:ℤ) → s.reg 77=(cursorAt o 6:ℤ) → s.reg 78=(cursorAt o 7:ℤ) → s.reg 80=(cursorAt o 9:ℤ) →
    s.closed=false → s.reg 82=(s.output.length:ℤ) → (∀i<cursorAt o 11,s.heap i=z.heap i) →
    let code:=(SingleCodes.words n h)[j]?.getD 0
    ∃t k, Logical.Executes n m (chain ((listOf src_trial).take 5)) s t k ∧ k ≤ 500*(M+1)+500*(n+1)^4 ∧
      t.heap=s.heap ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) ∧
      t.output=s.output++((arrange (Bits.normalized m W h)).owned v.val code).map Instr.lit := by sorry
