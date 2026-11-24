-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_native_live_production_table
-- name    : StableMSR.Recovery.NativeWriter.Production.native_live_production_table
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-23T23:21:10.908252+00:00
-- url     : https://prove2.me/theorems/ceaeca25-51f3-4edc-8308-68b114dfb198
-- title:
--   Generate the raw separator production table for a positive-scale representative
-- statement:
--   For each fixed $0<\varepsilon<1$, one native program handles all genuine representative slots with positive row scale. It emits the finite separator table’s chronological masks, child references, alternative joins, and final component information into the raw event representation. Its running time is $c\,\operatorname{cap}^D n^{bE(\varepsilon)}$ for uniform constants. The original scene, caller registers, and existing output columns are preserved.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_RegionalProductionTable
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

theorem StableMSR.Recovery.NativeWriter.Production.native_live_production_table :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  r%x.n∈WindowProfiles.keys x (r/x.n) → 0<scale x (r/x.n) →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    Stored x.n t.imem (regionalScript x (budget (e:ℝ)) (widthBound (e:ℝ)) r) := by sorry
