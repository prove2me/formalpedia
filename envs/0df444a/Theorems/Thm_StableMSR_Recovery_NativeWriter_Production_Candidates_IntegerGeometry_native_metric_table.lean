-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_native_metric_table
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.native_metric_table
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T00:18:33.012671+00:00
-- url     : https://prove2.me/theorems/24e59e18-9e20-4b05-a53b-1255a4243a70
-- title:
--   A native preprocessing pass encodes a region using exactly n²+1 distance queries
-- statement:
--   The program reads the scale of the requested scene row once, then caches each directed point-pair distance once. Comparisons among cached reals give a bounded integer rank and the three scale bands. Its running time is at most 200(1+rows+(1+n²)²). The signed integer table occupies one word per ordered pair, and all integer memory outside its lane, including the entire input scene and gate columns, is preserved.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_IntegerRegionalGeometry
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.native_metric_table :
    ∃cmd:Cmd,∀(x:World) (s:Store),Ready x s → 0<x.n → ∀r:ℕ,s.ptrs 3=(r:ℤ) → r<x.rows*x.n →
    ∃t z,Executes x.dist cmd s t z ∧
      z≤200*(1+x.rows+(1+x.n*x.n)^2) ∧ t.queries=s.queries+x.n*x.n+1 ∧
      Ready x t ∧ (∀j<6,t.ptrs j=s.ptrs j) ∧
      (∀q:ℤ,(∀j:ℕ,q≠cell 6 j) → t.imem q=s.imem q) ∧ Prepared x (scale x (r/x.n)) t.imem := by sorry
