-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_rows_and_two_tables
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.rows_and_two_tables
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-24T16:28:54.651879+00:00
-- url     : https://prove2.me/theorems/58eb27a8-db88-43df-9886-9ce9aa6f6f9c
-- title:
--   The exact separator row tape and the two graph bitmaps at their initialized addresses
-- statement:
--   On each live regional input, run geometry construction and row enumeration up to the root requests. The emitted list must be the canonical row tape, and the two arrays at their prescribed offsets must encode the active vertices and directed adjacency. The required charge is $c\\,\\mathrm{cap}^D n^{bE(\\varepsilon)}$ uniformly in the calibration parameter. All register and cursor conclusions are discharged separately.
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_InitializedSeparatorTraversal
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.rows_and_two_tables :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
    ∃t k,Logical.Executes x.n s.imem (Logical.chain (Logical.middleList.take 3)) u t k ∧
      k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      t.output=rowTape CandidateRAM.Naming.name d (widthBound (e:ℝ)) ∧
      (let o:=Logical.offsets d.n (Logical.sizes d.n (budget (e:ℝ)))
       (∀j<d.n,1 ≤ t.heap (Logical.cursorAt o 0+j) ↔ d.active j=true) ∧
       (∀j<d.n,∀v<d.n,1 ≤ t.heap (Logical.cursorAt o 4+(j*d.n+v)) ↔ d.edge j v=true)) := by sorry
