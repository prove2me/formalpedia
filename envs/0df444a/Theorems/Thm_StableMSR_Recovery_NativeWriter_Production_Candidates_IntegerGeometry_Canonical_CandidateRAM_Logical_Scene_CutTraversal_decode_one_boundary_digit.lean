-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_decode_one_boundary_digit
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.decode_one_boundary_digit
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T00:58:51.25582+00:00
-- url     : https://prove2.me/theorems/bc20881f-a3cd-4f71-8353-602b4a90d456
-- title:
--   One reverse boundary digit updates exactly one scratch cell
-- statement:
--   A single iteration reads the next boundary vertex in reverse order, writes the remainder to its scratch cell and carries the quotient to the next digit. The permission bit at the immutable table address determines whether the feasibility flag is cleared. Every other heap cell, the output, and registers outside the displayed write set are preserved. The bound includes both charged divisions.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.4 and A.6. Implementation lemma for the boundary assignment loop.

import Definitions.Def_StableMSR_SeparatorOrdinals
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.decode_one_boundary_digit (n : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (M q i back v vec buf bits : ℕ) (hM : 0 < M) (one : s.reg 6 = 1)
    (base : s.reg 70 = (M:ℤ)) (remReg : s.reg 252 = (q:ℤ))
    (len : s.reg 243 = ((back+i+1:ℕ):ℤ)) (idx : s.reg 245 = (i:ℤ))
    (vector : s.reg 242 = (vec:ℤ)) (buffer : s.reg 250 = (buf:ℤ)) (table : s.reg 81 = (bits:ℤ))
    (atVertex : s.heap (vec+back) = (v:ℤ))
    (separate : bits+(v*M+q%M) ≠ buf+v) :
    let loopCode := ((listOf ordinalBody)[3]?).getD .skip
    let step := match ((listOf loopCode)[3]? : Option Program) with
      | some (Program.loop _ _ body) => ((listOf body)[0]?).getD .skip
      | _ => .skip
    ∃ t k, Logical.Executes n m step s t k ∧ k ≤ 400+6*M+16*(q/M) ∧
      t.reg 252 = ((q/M:ℕ):ℤ) ∧ t.reg 255 = ((q%M:ℕ):ℤ) ∧
      t.reg 253 = (if 1 ≤ s.heap (bits+(v*M+q%M)) then s.reg 253 else 0) ∧
      t.heap = Function.update s.heap (buf+v) ((q%M:ℕ):ℤ) ∧
      t.output = s.output ∧ t.closed = s.closed ∧
      ∀ j, j ∉ [1095,1093,1092,1090,254,1097,255,1100,252,1111,1110,1108,1107,1115,253] →
        t.reg j = s.reg j := by sorry
