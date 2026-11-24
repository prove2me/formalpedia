-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_native_integer_candidate_source
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.native_integer_candidate_source
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-24T00:17:07.425497+00:00
-- url     : https://prove2.me/theorems/356aa24f-3511-4604-9278-6ee8f34f70e8
-- title:
--   Generate the exact candidate tape from a bounded integer matrix
-- statement:
--   Given the region labels and an n by n table of nonnegative integers below 10(n²+1), enumerate the ordered separator candidates at the fixed integer scale n²+1. Use only integer operations and pointer tests, with the zero distance oracle. Output the literal masks, local tests and injectively named keys within the mission’s stability exponent.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_IntegerRegionalGeometry
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.native_integer_candidate_source :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,IntegerCmd cmd ∧
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Executes (fun (_ _:Fin x.n)=>(0:ℝ)) cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      Input x.n t.imem (tape enc (data x s.imem r (budget (e:ℝ))) (widthBound (e:ℝ))) := by sorry
