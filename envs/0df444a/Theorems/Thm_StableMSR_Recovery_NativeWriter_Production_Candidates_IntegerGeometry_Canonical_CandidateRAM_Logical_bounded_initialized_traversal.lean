-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_bounded_initialized_traversal
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.bounded_initialized_traversal
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T02:36:45.1848+00:00
-- url     : https://prove2.me/theorems/c8dfe400-f298-4d98-9efe-0953a3eaeded
-- title:
--   Correctness and uniform cost of geometry construction and separator traversal
-- statement:
--   From the eleven initialized scratch arrays, execute the specified geometry code, the traversal by component size and separator, and the concluding root-component requests. Prove that these produce the canonical row tape followed by exactly the requests for components at empty boundary, within $c\\,\\mathrm{cap}^D n^{bE(\\varepsilon)}$ charges. This is the remaining algorithmic claim for the certified concrete source.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_InitializedSeparatorTraversal
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.bounded_initialized_traversal :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∃t k,Logical.Executes x.n s.imem (chain middleList) u t k ∧
      k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      t.output=middleRecords (integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ)) := by sorry
