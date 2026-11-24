-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_root_requests_exact
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.root_requests_exact
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T16:32:16.801486+00:00
-- url     : https://prove2.me/theorems/5aaebedc-1da5-4eb6-bc06-fae6287e2d12
-- title:
--   The full root loop appends the canonical requests for all components in reference order
-- statement:
--   Given the active-vertex and adjacency tables for an instance on $n$ vertices, the final source loop appends exactly one request for each component selected by the reference enumeration, in its prescribed order. The boundary assignment in each request is empty. This holds for an arbitrary previously emitted stream and takes at most $10000(n+1)^5$ source charges.
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_RootComponentRequests
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.root_requests_exact (d:Instance) (input:ℤ → ℤ) (s:Logical.State) (ok:Root.inputs d s) :
    ∃t k,Logical.Executes d.n input (Logical.chain Root.suffixOps) s t k ∧ k ≤ 10000*(d.n+1)^5 ∧
      t.output=s.output++Root.requests d ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) := by sorry
