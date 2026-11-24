-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_native_unfiltered_candidate_source
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.native_unfiltered_candidate_source
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-23T23:38:05.136834+00:00
-- url     : https://prove2.me/theorems/b79f9b78-6cc8-4dd3-b428-3d8f7458b458
-- title:
--   Enumerate all separator candidates without evaluating their child dependencies
-- statement:
--   For a positive-scale representative, a native program lists each tight row and every pivot and menu-label candidate in separator order. Its tape contains owned-block point memberships, local consistency bits, and numerical names for the requested and installed keys. Equal keys receive equal names, and distinct keys receive distinct names. The uniform time bound is $c\,\operatorname{cap}^{D}n^{bE(\varepsilon)}$.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.native_unfiltered_candidate_source :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  r%x.n∈WindowProfiles.keys x (r/x.n) → 0<scale x (r/x.n) →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      let d:=SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) (budget (e:ℝ))
      Input x.n t.imem (tape enc d (widthBound (e:ℝ))) := by sorry
