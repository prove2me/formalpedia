-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_native_canonical_candidate_source
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.native_canonical_candidate_source
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-24T01:03:10.630325+00:00
-- url     : https://prove2.me/theorems/96982b12-39e9-4727-82ba-ab800b56b1eb
-- title:
--   Realize the computable canonical candidate tape on the integer RAM
-- statement:
--   For each fixed stability parameter, construct a uniform integer RAM routine which enumerates the canonical separator tape from the scene labels and a bounded integer distance matrix. The instructions carry canonically sorted literal masks, injectively named tight keys and local compatibility bits. The routine must preserve the designated input registers and earlier output columns and satisfy the uniform $c\,\mathrm{cap}^D n^{bE(\varepsilon)}$ time bound.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.native_canonical_candidate_source :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,IntegerCmd cmd ∧
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Executes (fun (_ _:Fin x.n)=>(0:ℝ)) cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      Input x.n t.imem (tape enc (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ))) := by sorry
