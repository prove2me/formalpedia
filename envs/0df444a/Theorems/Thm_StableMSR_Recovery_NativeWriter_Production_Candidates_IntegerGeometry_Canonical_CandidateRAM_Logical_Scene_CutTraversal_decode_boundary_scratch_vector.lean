-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_decode_boundary_scratch_vector
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.decode_boundary_scratch_vector
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-26T00:56:47.254999+00:00
-- url     : https://prove2.me/theorems/34341de6-4952-509d-b789-6b50c37aaf10
-- title:
--   The full boundary decoder preserves the input tables and writes the base digits
-- statement:
--   The complete reverse boundary loop writes the base-M expansion of an ordinal to its vertex-indexed scratch cells. Its feasibility flag survives exactly when all the tested table entries pass, with the incoming flag retained in that case. The theorem specifies the entire heap, the final quotient, and the cost, including an empty boundary.
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.decode_boundary_scratch_vector (n : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (M q L vec buf bits : ℕ) (vertex : ℕ → ℕ)
    (pos : 0 < M) (one : s.reg 6 = 1) (base : s.reg 70 = (M:ℤ))
    (initial : s.reg 252 = (q:ℤ)) (len : s.reg 243 = (L:ℤ))
    (vector : s.reg 242 = (vec:ℤ)) (buffer : s.reg 250 = (buf:ℤ)) (table : s.reg 81 = (bits:ℤ))
    (readVertex : ∀ i < L, s.heap (vec+(L-1-i)) = (vertex i:ℤ))
    (bounded : ∀ i < L, vertex i < n) (vecEnd : vec+L ≤ buf) (tableEnd : bits+n*M ≤ buf) :
    let loopCode := ((listOf ordinalBody)[3]?).getD .skip
    let digit := fun i => (q / M^i) % M
    let heapAt := (List.range L).foldl (fun (h : ℕ → ℤ) i =>
      Function.update h (buf+vertex i) (digit i:ℤ)) s.heap
    let ok := (List.range L).all (fun i => decide (1 ≤ s.heap (bits+(vertex i*M+digit i))))
    ∃ t k, Logical.Executes n m loopCode s t k ∧ k ≤ 9+L*(405+6*M+16*q) ∧
      t.reg 252 = ((q/M^L:ℕ):ℤ) ∧ t.heap = heapAt ∧
      t.reg 253 = (if ok then s.reg 253 else 0) ∧
      t.output = s.output ∧ t.closed = s.closed ∧
      ∀ j, j ∉ [245,1089,1095,1093,1092,1090,254,1097,255,1100,252,1111,1110,1108,1107,1115,253] →
        t.reg j = s.reg j := by sorry
