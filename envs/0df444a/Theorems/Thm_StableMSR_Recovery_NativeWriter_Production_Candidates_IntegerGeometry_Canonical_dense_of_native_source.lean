-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_dense_of_native_source
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.dense_of_native_source
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T01:46:28.560344+00:00
-- url     : https://prove2.me/theorems/38694732-2134-4eca-ae25-1d59a4fc12e6
-- title:
--   The physical dense circuit writer follows from a canonically ordered native candidate source
-- statement:
--   An integer source that realizes the sorted candidate tape, with its stated time and memory frame, suffices for the original dense-circuit theorem. The proof includes gate counting, native filtering and replay, header control, placement of every regional packet, and final dense column formatting. The native source is an explicit premise of the implication.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.dense_of_native_source (source : ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,IntegerCmd cmd ∧
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Executes (fun (_ _:Fin x.n)=>(0:ℝ)) cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      Input x.n t.imem (tape enc (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ)))) : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd := by sorry
