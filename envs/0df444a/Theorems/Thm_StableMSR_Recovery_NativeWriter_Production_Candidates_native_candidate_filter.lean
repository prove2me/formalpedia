-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_native_candidate_filter
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.native_candidate_filter
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T23:36:59.572472+00:00
-- url     : https://prove2.me/theorems/23fa442c-d1ac-4656-8759-ca42078863c5
-- title:
--   A two-pass native RAM filter computes every accepted separator event and child handle
-- statement:
--   An $n$-point scene contains an unfiltered candidate tape of length $M$. A fixed native command transforms it into the exact accepted production stream and signed exit, preserving the input scene and the six existing gate and directory columns. Its running time is at most $$A(1+n)(1+M)$$ for an absolute constant $A$, independently of the magnitudes of all key names. Arbitrary initial scratch memory is allowed.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.native_candidate_filter :
    ∃ (A:ℕ) (cmd:Cmd),∀(x:World) (s:Store) (xs:List Candidates.Instr),Ready x s → Input x.n s.imem xs →
    ∃t z,Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+xs.length) ∧ Ready x t ∧
      (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧ (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
      Stored x.n t.imem (Candidates.eval xs) := by sorry
