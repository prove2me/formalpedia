-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_native_slot_classification
-- name    : StableMSR.Recovery.NativeWriter.Production.native_slot_classification
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T23:21:53.728033+00:00
-- url     : https://prove2.me/theorems/cdbb0a9c-8ed0-4fc3-846d-f52a68e98a79
-- title:
--   Classify every flattened region slot on the native RAM
-- statement:
--   Given an $n$-point scene with $S$ rows and a slot $0\le r<Sn$, one fixed command distinguishes three cases. It returns $-1$ if the point is not the least representative of its label, $-2$ if it is the representative and the row scale is nonpositive, and $0$ if it is the representative of a positive-scale row. The command preserves all integer memory and the first six pointer registers, and takes at most $A(1+n)(1+S)$ steps for an absolute constant $A$.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_RegionalProductionTable
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit
open scoped Classical

theorem StableMSR.Recovery.NativeWriter.Production.native_slot_classification :
  ∃ (A:ℕ) (cmd:Cmd),∀(x:World) (s:Store) (r:ℕ),Ready x s → s.ptrs 3=(r:ℤ) → 0<x.n → r<x.rows*x.n →
    ∃t z,Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+x.rows) ∧ t.imem=s.imem ∧
      (∀i<6,t.ptrs i=s.ptrs i) ∧
      t.ptrs 6=(if r%x.n∈WindowProfiles.keys x (r/x.n) then if 0<scale x (r/x.n) then 0 else -2 else -1) ∧
      t.ptrs 14 = -1 := by sorry
