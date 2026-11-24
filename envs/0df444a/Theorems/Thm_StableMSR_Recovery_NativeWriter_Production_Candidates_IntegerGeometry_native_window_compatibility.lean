-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_native_window_compatibility
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.native_window_compatibility
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T00:37:48.230642+00:00
-- url     : https://prove2.me/theorems/5ba76233-6129-452e-b52d-ffa8ad9f19ed
-- title:
--   A cubic-time native integer test for window compatibility
-- statement:
--   Given two n by n block-membership matrices and the membership bits for two owner fibers, a register program tests the mission’s local window compatibility exactly. It scans each row pair for four witnesses: a touch in the first fiber, a touch in the second, an intersection and a disagreement. It uses at most 100(1+n)³ instructions, makes zero distance queries and preserves both memories. Empty or repeated rows are allowed.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_IntegerRegionalGeometry
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.native_window_compatibility :
  ∃cmd:Cmd,IntegerCmd cmd ∧ ∀(n:ℕ) (d:Fin n→Fin n→ℝ) (s:Store) (own:Fin n→Fin n) (a b:Fin n)
    (L R:Fin n→Cluster n),s.ptrs 0=(n:ℤ) →
    (∀i p:Fin n,s.imem (s.ptrs 30+(i.val:ℤ)*(n:ℤ)+(p.val:ℤ))=(if p∈L i then 1 else 0) ∧
      s.imem (s.ptrs 31+(i.val:ℤ)*(n:ℤ)+(p.val:ℤ))=(if p∈R i then 1 else 0)) →
    (∀p:Fin n,s.imem (s.ptrs 32+(p.val:ℤ))=(if own p=a then 1 else 0) ∧
      s.imem (s.ptrs 33+(p.val:ℤ))=(if own p=b then 1 else 0)) →
    ∃t z,Executes d cmd s t z ∧ z≤100*(1+n)^3 ∧ t.imem=s.imem ∧ t.mem=s.mem ∧ t.queries=s.queries ∧
      (∀j<6,t.ptrs j=s.ptrs j) ∧ t.ptrs 37=(if compatible own a b (Finset.univ.image L) (Finset.univ.image R) then 1 else 0) := by sorry
