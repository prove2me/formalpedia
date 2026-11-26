-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_regional_compatibility_from_tables
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.regional_compatibility_from_tables
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T03:13:40.266647+00:00
-- url     : https://prove2.me/theorems/50c98e51-88f4-57ce-903e-4e3010b5819b
-- title:
--   Read compatibility directly from the represented regional menus
-- statement:
--   With the regional menu and membership tables in memory, the complete compatibility source returns exactly the test bit for the two chosen vertex labels in the normalized geometric instance. It preserves the heap and output and has an explicit uniform cost bound.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.regional_compatibility_from_tables (n h : ℕ) (m : ℤ→ℤ) (W : Cluster n) (a b : Fin n) (x y : ℕ) (v z s : Logical.State)
    (menus : Scene.RegionalMenus m W h v z) :
    let M := sizes n h
    let o := offsets n M
    ∀ (_ : x<M) (_ : y<M), s.reg 6=1 → s.reg 64=(n:ℤ) → s.reg 70=(M:ℤ) →
      s.reg 203=(a.val:ℤ) → s.reg 204=(x:ℤ) → s.reg 205=(b.val:ℤ) → s.reg 206=(y:ℤ) →
      s.reg 77=(cursorAt o 6:ℤ) → s.reg 79=(cursorAt o 8:ℤ) → s.reg 80=(cursorAt o 9:ℤ) →
      (∀q<cursorAt o 11,s.heap q=z.heap q) →
    let c := (SingleCodes.words n h)[x]?.getD 0
    let k := (SingleCodes.words n h)[y]?.getD 0
    ∃t cost, Logical.Executes n m src_fits s t cost ∧ cost≤1000*(M+1)+1000*(n+1)^3 ∧
      t.reg 217=(if (Bits.normalized m W h).test a.val b.val c k then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by sorry
