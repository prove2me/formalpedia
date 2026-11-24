-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_native_block_order_key
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.native_block_order_key
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T01:10:39.135032+00:00
-- url     : https://prove2.me/theorems/95213966-bcfa-4e76-bb89-ba68c79493eb
-- title:
--   A linear-time integer RAM key for the lexicographic order of literal masks
-- statement:
--   For a binary row of length $n$, a fixed integer RAM routine computes a key $k<2^n$ in at most $7+11n$ steps, preserving memory, the query counter and the input registers. For rows of the same length, the keys compare exactly as the increasing lists of their marked point indices. The routine handles empty masks, shared prefixes and repeated masks.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.native_block_order_key :
  ∃(cmd:Cmd) (key:List Bool→ℕ),IntegerCmd cmd ∧
    (∀bs:List Bool,key bs<2^bs.length) ∧
    (∀(a b:List Bool),a.length=b.length →
      let points:=fun xs:List Bool=>(List.range xs.length).filter (fun i=>(xs[i]?).getD false)
      key a<key b ↔ points a < points b) ∧
    ∀(n:ℕ) (d:Fin n→Fin n→ℝ) (s:Store) (bs:List Bool),s.ptrs 0=(bs.length:ℤ) →
      (∀j (hj:j<bs.length),s.imem (s.ptrs 30+(j:ℤ))=(if bs[j] then 1 else 0)) →
      ∃t z,Executes d cmd s t z ∧ z≤7+11*bs.length ∧ t.ptrs 44=(key bs:ℤ) ∧ t.imem=s.imem ∧ t.queries=s.queries ∧ (∀j<6,t.ptrs j=s.ptrs j) := by sorry
